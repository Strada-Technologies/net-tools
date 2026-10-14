//! macOS: a socket per remote, connected to it and bound to the
//! shared socket's port on the local address the route to that remote uses.
//!
//! macOS charges an unconnected UDP socket a route lookup and a temporary
//! connect on every send (about 15 µs per datagram against 3.4 µs connected),
//! and its receive path drops datagrams beyond roughly 70k per second that a
//! connected socket takes at more than 235k. At QUIC's ~1.4 KB packets that
//! caps an unconnected socket near 800 Mbit/s, whatever the link.
//!
//! The connected socket binds the specific local address with `SO_REUSEADDR`
//! only, which BSD allows next to the shared socket's wildcard binding: the
//! remote's datagrams arrive on it (exact match) while every other remote's
//! still arrive on the shared socket, replies leave from the same port so NAT
//! mappings and hole punching are unchanged, and no other process can share
//! the port. `NETWATCH_CONNECTED_PEERS=0` turns it off.

use std::{
    collections::HashMap,
    io,
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr},
    sync::{
        Arc, Mutex, MutexGuard,
        atomic::{AtomicU8, AtomicU64, Ordering::Relaxed},
    },
    task::{Context, Poll},
    time::{Duration, Instant},
};

use atomic_waker::AtomicWaker;
use noq_udp::{RecvMeta, Transmit};
use tokio::io::Interest;
use tracing::{debug, warn};

use crate::IpFamily;

/// Most remotes with a socket of their own; the least recently used gives way.
const MAX_SOCKETS: usize = 64;
/// A remote unused for this long gives its socket back.
const IDLE: Duration = Duration::from_secs(60);
/// After its connected socket fails, a remote stays on the shared socket this long.
const RETRY_AFTER: Duration = Duration::from_secs(30);

pub(super) fn enabled() -> bool {
    #[cfg(target_os = "macos")]
    {
        static ON: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
            std::env::var_os("NETWATCH_CONNECTED_PEERS").is_none_or(|value| value != "0")
        });
        *ON
    }
    #[cfg(not(target_os = "macos"))]
    {
        false
    }
}

#[derive(Debug)]
struct PeerSocket {
    remote: SocketAddr,
    /// The address the socket is bound to.
    local: IpAddr,
    socket: tokio::net::UdpSocket,
    state: noq_udp::UdpSocketState,
    /// ECN bits currently set on the socket; `u8::MAX` before the first send.
    ecn: AtomicU8,
    /// Milliseconds after [`PeerSockets::epoch`] of the last send or receive.
    last_used: AtomicU64,
}

#[derive(Debug, Default)]
struct Sockets {
    by_remote: HashMap<SocketAddr, Arc<PeerSocket>>,
    /// Receive order, rotated on every poll so one busy remote can't starve the
    /// rest. Replaced rather than modified, so a poll takes it without copying.
    order: Arc<[Arc<PeerSocket>]>,
    next: usize,
    /// Remotes whose socket failed, with the time they may be tried again.
    failed: HashMap<SocketAddr, u64>,
}

impl Sockets {
    fn insert(&mut self, peer: Arc<PeerSocket>) {
        self.by_remote.insert(peer.remote, peer.clone());
        self.order = self.order.iter().cloned().chain([peer]).collect();
    }

    fn remove(&mut self, remote: SocketAddr) {
        if self.by_remote.remove(&remote).is_some() {
            self.order = self
                .order
                .iter()
                .filter(|peer| peer.remote != remote)
                .cloned()
                .collect();
        }
    }
}

#[derive(Debug)]
pub(super) struct PeerSockets {
    sockets: Mutex<Sockets>,
    /// Woken when a socket opens, which the receive side may be parked without.
    opened: AtomicWaker,
    epoch: Instant,
}

impl PeerSockets {
    pub(super) fn new() -> Self {
        Self {
            sockets: Mutex::default(),
            opened: AtomicWaker::new(),
            epoch: Instant::now(),
        }
    }

    fn now(&self) -> u64 {
        self.epoch.elapsed().as_millis() as u64
    }

    fn lock(&self) -> MutexGuard<'_, Sockets> {
        self.sockets.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Drops every connected socket. After a rebind or a network change a
    /// connected socket keeps the route and local address it chose at connect,
    /// so they are opened again on the next send.
    pub(super) fn clear(&self) {
        *self.lock() = Sockets::default();
    }

    /// `None` when the transmit belongs on the shared socket; see [`Self::peer_for`].
    pub(super) fn poll_send(
        &self,
        cx: &mut Context<'_>,
        local: SocketAddr,
        transmit: &Transmit<'_>,
    ) -> Option<Poll<io::Result<()>>> {
        let peer = self.peer_for(local, transmit)?;
        loop {
            match peer.socket.poll_send_ready(cx) {
                Poll::Pending => return Some(Poll::Pending),
                Poll::Ready(Err(err)) => {
                    self.drop_broken(&peer, &err);
                    return None;
                }
                Poll::Ready(Ok(())) => match self.send_now(&peer, transmit) {
                    Err(err) if err.kind() == io::ErrorKind::WouldBlock => continue,
                    Err(err) if !is_lost_datagram(&err) => {
                        self.drop_broken(&peer, &err);
                        return None;
                    }
                    _ => return Some(Poll::Ready(Ok(()))),
                },
            }
        }
    }

    pub(super) fn try_send(
        &self,
        local: SocketAddr,
        transmit: &Transmit<'_>,
    ) -> Option<io::Result<()>> {
        let peer = self.peer_for(local, transmit)?;
        match self.send_now(&peer, transmit) {
            Err(err) if err.kind() == io::ErrorKind::WouldBlock => Some(Err(err)),
            Err(err) if !is_lost_datagram(&err) => {
                self.drop_broken(&peer, &err);
                None
            }
            _ => Some(Ok(())),
        }
    }

    /// Datagrams waiting on any connected socket. Registers for readiness on
    /// every connected socket it finds empty, and for a socket opening, so the
    /// caller is woken by either.
    pub(super) fn poll_recv(
        &self,
        cx: &mut Context<'_>,
        bufs: &mut [io::IoSliceMut<'_>],
        meta: &mut [RecvMeta],
    ) -> Option<io::Result<usize>> {
        if !enabled() {
            return None;
        }
        // Before the sockets are read, so one opened after the read still wakes the caller.
        self.opened.register(cx.waker());
        let (order, start) = {
            let mut sockets = self.lock();
            let start = sockets.next;
            sockets.next = sockets.next.wrapping_add(1);
            (sockets.order.clone(), start)
        };
        for i in 0..order.len() {
            let peer = &order[(start + i) % order.len()];
            loop {
                match peer.socket.poll_recv_ready(cx) {
                    Poll::Pending => break,
                    Poll::Ready(Err(err)) => {
                        self.drop_broken(peer, &err);
                        break;
                    }
                    Poll::Ready(Ok(())) => {
                        match peer.socket.try_io(Interest::READABLE, || {
                            peer.state.recv((&peer.socket).into(), bufs, meta)
                        }) {
                            Ok(count) => {
                                peer.last_used.store(self.now(), Relaxed);
                                return Some(Ok(count));
                            }
                            Err(err)
                                if err.kind() == io::ErrorKind::WouldBlock
                                    || is_lost_datagram(&err) =>
                            {
                                continue;
                            }
                            Err(err) => {
                                self.drop_broken(peer, &err);
                                break;
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// The remote's connected socket, opened on first use. `None` sends the
    /// transmit on the shared socket instead: switched off, a multi-segment
    /// transmit (a connected socket sends one datagram per call, and a segment
    /// sent before a `Pending` would go out twice on the retry), a source
    /// address other than the one the socket is bound to, which only the
    /// shared socket can send from, or no connected socket for this remote.
    fn peer_for(&self, local: SocketAddr, transmit: &Transmit<'_>) -> Option<Arc<PeerSocket>> {
        if !enabled()
            || transmit
                .segment_size
                .is_some_and(|size| size < transmit.contents.len())
        {
            return None;
        }
        let peer = self.open(local, transmit.destination)?;
        if transmit
            .src_ip
            .is_some_and(|ip| ip.to_canonical() != peer.local)
        {
            return None;
        }
        Some(peer)
    }

    fn open(&self, local: SocketAddr, remote: SocketAddr) -> Option<Arc<PeerSocket>> {
        let now = self.now();
        let mut sockets = self.lock();
        if let Some(peer) = sockets.by_remote.get(&remote) {
            return Some(peer.clone());
        }
        if sockets
            .failed
            .get(&remote)
            .is_some_and(|retry_at| now < *retry_at)
        {
            return None;
        }
        let ip = remote.ip();
        if IpFamily::from(local.ip()) != IpFamily::from(ip)
            || ip.is_unspecified()
            || ip.is_multicast()
        {
            return None;
        }

        let idle = IDLE.as_millis() as u64;
        let stale: Vec<SocketAddr> = sockets
            .order
            .iter()
            .filter(|peer| now.saturating_sub(peer.last_used.load(Relaxed)) >= idle)
            .map(|peer| peer.remote)
            .collect();
        for stale in stale {
            sockets.remove(stale);
        }
        if sockets.order.len() >= MAX_SOCKETS
            && let Some(oldest) = sockets
                .order
                .iter()
                .min_by_key(|peer| peer.last_used.load(Relaxed))
                .map(|peer| peer.remote)
        {
            sockets.remove(oldest);
        }

        match connect(local, remote) {
            Ok((socket, state, bound)) => {
                let peer = Arc::new(PeerSocket {
                    remote,
                    local: bound.ip().to_canonical(),
                    socket,
                    state,
                    ecn: AtomicU8::new(u8::MAX),
                    last_used: AtomicU64::new(now),
                });
                sockets.failed.remove(&remote);
                sockets.insert(peer.clone());
                drop(sockets);
                debug!(%remote, local = %bound, "connected socket opened");
                self.opened.wake();
                Some(peer)
            }
            Err(err) => {
                debug!(%remote, ?err, "connected socket failed, using the shared socket");
                sockets
                    .failed
                    .insert(remote, now + RETRY_AFTER.as_millis() as u64);
                None
            }
        }
    }

    fn send_now(&self, peer: &PeerSocket, transmit: &Transmit<'_>) -> io::Result<()> {
        let ecn = transmit.ecn.map_or(0, |ecn| ecn as u8);
        if peer.ecn.load(Relaxed) != ecn {
            if let Err(err) = set_ecn(&peer.socket, peer.remote, ecn) {
                debug!(remote = %peer.remote, ?err, "could not set ECN on a connected socket");
            }
            peer.ecn.store(ecn, Relaxed);
        }
        peer.socket.try_send(transmit.contents)?;
        peer.last_used.store(self.now(), Relaxed);
        Ok(())
    }

    /// Closes the socket and leaves its remote on the shared socket for [`RETRY_AFTER`].
    fn drop_broken(&self, peer: &Arc<PeerSocket>, err: &io::Error) {
        let mut sockets = self.lock();
        if sockets
            .by_remote
            .get(&peer.remote)
            .is_some_and(|current| Arc::ptr_eq(current, peer))
        {
            warn!(remote = %peer.remote, ?err, "connected socket failed, using the shared socket");
            sockets.remove(peer.remote);
            sockets
                .failed
                .insert(peer.remote, self.now() + RETRY_AFTER.as_millis() as u64);
        }
    }
}

/// Errors the shared socket's sender also counts as a lost datagram and
/// carries on from: ICMP reports, which a connected socket returns on a later
/// call and an unconnected one never sees, a full interface queue, and a path
/// MTU probe larger than the link. Passing one up would end the path, for
/// example when the remote was not yet listening (port unreachable).
fn is_lost_datagram(err: &io::Error) -> bool {
    if matches!(
        err.kind(),
        io::ErrorKind::ConnectionRefused
            | io::ErrorKind::HostUnreachable
            | io::ErrorKind::NetworkUnreachable
            | io::ErrorKind::NetworkDown
    ) {
        return true;
    }
    #[cfg(unix)]
    if matches!(
        err.raw_os_error(),
        Some(libc::EHOSTDOWN | libc::ENOBUFS | libc::EMSGSIZE)
    ) {
        return true;
    }
    false
}

/// Binds the local address the route to `remote` uses, on `local`'s port, and
/// connects. Binding the specific address rather than the wildcard is what
/// lets this socket share the port without `SO_REUSEPORT` on the shared one.
fn connect(
    local: SocketAddr,
    remote: SocketAddr,
) -> io::Result<(tokio::net::UdpSocket, noq_udp::UdpSocketState, SocketAddr)> {
    let unspecified: IpAddr = match remote {
        SocketAddr::V4(_) => Ipv4Addr::UNSPECIFIED.into(),
        SocketAddr::V6(_) => Ipv6Addr::UNSPECIFIED.into(),
    };
    let route = std::net::UdpSocket::bind((unspecified, 0))?;
    route.connect(remote)?;
    let mut bind_addr = route.local_addr()?;
    drop(route);
    bind_addr.set_port(local.port());

    let network = IpFamily::from(remote.ip());
    let socket = socket2::Socket::new(
        network.into(),
        socket2::Type::DGRAM,
        Some(socket2::Protocol::UDP),
    )?;
    let _ = socket.set_recv_buffer_size(super::SOCKET_BUFFER_SIZE);
    let _ = socket.set_send_buffer_size(super::SOCKET_BUFFER_SIZE);
    if network == IpFamily::V6 {
        socket.set_only_v6(true)?;
    }
    socket.set_reuse_address(true)?;
    socket.bind(&bind_addr.into())?;
    socket.connect(&remote.into())?;
    socket.set_nonblocking(true)?;
    let socket = tokio::net::UdpSocket::from_std(socket.into())?;
    let state = noq_udp::UdpSocketState::new((&socket).into())?;
    Ok((socket, state, bind_addr))
}

/// Marks the socket's datagrams with `ecn`. The shared socket marks each one
/// in a control message; a connected socket sends without one, and a
/// connection keeps the same codepoint, so it is set only when it changes.
#[cfg(unix)]
fn set_ecn(socket: &tokio::net::UdpSocket, remote: SocketAddr, ecn: u8) -> io::Result<()> {
    use std::os::fd::AsRawFd;
    let (level, name) = match remote {
        SocketAddr::V4(_) => (libc::IPPROTO_IP, libc::IP_TOS),
        SocketAddr::V6(_) => (libc::IPPROTO_IPV6, libc::IPV6_TCLASS),
    };
    let value = libc::c_int::from(ecn);
    // SAFETY: the fd is open for the lifetime of `socket`, and `value` outlives the call.
    let rc = unsafe {
        libc::setsockopt(
            socket.as_raw_fd(),
            level,
            name,
            (&value as *const libc::c_int).cast(),
            std::mem::size_of::<libc::c_int>() as libc::socklen_t,
        )
    };
    if rc == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(not(unix))]
fn set_ecn(_socket: &tokio::net::UdpSocket, _remote: SocketAddr, _ecn: u8) -> io::Result<()> {
    Ok(())
}
