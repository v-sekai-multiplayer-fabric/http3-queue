namespace Http3Queue.WakeLoop

/-- A model of the picoquic network-thread packet loop and the wake-up flood that
    wedges it. In `sockloop.c` the loop's wake-up branch is MUTUALLY EXCLUSIVE with
    the receive/send branch: an iteration that observes a wake byte runs only the
    work-queue drain and then re-polls — it never reads the UDP socket and never
    sends. The Godot backend calls `picoquic_wake_up_network_thread` once per
    outbound datagram, and the server broadcasts positions to every client every
    few ticks. Once wake-ups arrive faster than the loop iterates, the wake pipe
    never empties, so every iteration takes the wake branch and BOTH directions
    starve — the thread stays alive (`ret == 0`) but stops processing all packets.

    The fix is to COALESCE wakes: keep one "wake pending" flag and only write a
    wake byte when none is outstanding, so at most one wake is in flight. Then a
    wake iteration is always followed by a receive/send iteration and neither side
    starves. We model both and have Plausible/▸proof show the unguarded loop starves
    inbound while the coalesced loop never does. -/

structure St where
  wake  : Nat    -- bytes pending in the wake pipe
  flag  : Bool   -- "a wake is already pending" (the coalescing flag; fix only)
  rxq   : Nat    -- inbound packets waiting at the UDP socket
  rcvd  : Nat    -- inbound packets the loop has actually processed
  deriving Repr, DecidableEq

def init : St := { wake := 0, flag := false, rxq := 0, rcvd := 0 }

/-- An inbound packet lands at the socket (a client sent us something). -/
def rxArrive (s : St) : St := { s with rxq := s.rxq + 1 }

/-- The main thread posts an outbound datagram and wakes the network thread.
    UNGUARDED: every post writes a wake byte (the bug). -/
def postWakeRaw (s : St) : St := { s with wake := s.wake + 1 }

/-- COALESCED: only write a wake byte when none is outstanding (the fix). -/
def postWakeCoalesced (s : St) : St :=
  if s.flag then s else { s with wake := s.wake + 1, flag := true }

/-- BUGGY loop iteration (today's sockloop.c): the wake branch is MUTUALLY
    EXCLUSIVE with receive. A non-empty wake pipe makes the loop drain the pipe and
    re-poll, SKIPPING the socket read entirely; only an iteration with an empty pipe
    reads inbound. So a steady wake stream starves inbound forever. -/
def iterExcl (s : St) : St :=
  if s.wake > 0 then
    { s with wake := 0, flag := false }         -- wake branch: drain pipe, NO rx
  else
    { s with rcvd := s.rcvd + s.rxq, rxq := 0 } -- rx branch: process all inbound

/-- FIXED loop iteration: a woken iteration ALSO drains the socket — wake and
    receive are no longer mutually exclusive. Inbound is serviced every iteration
    regardless of the wake pipe, so no wake stream can starve it. -/
def iterIncl (s : St) : St :=
  { s with wake := 0, flag := false, rcvd := s.rcvd + s.rxq, rxq := 0 }

/-- The adversarial load: one packet waits, then the producer posts a wake
    immediately before every loop iteration — the exact "wake faster than we drain"
    schedule. Parameterised by the wake op and the iteration so the buggy and fixed
    loops run over the SAME worst case. -/
def adversarial (post iterf : St → St) : Nat → St → St
  | 0,     s => s
  | n + 1, s => adversarial post iterf n (iterf (post s))

def runAdversarial (post iterf : St → St) (n : Nat) : St :=
  adversarial post iterf n (rxArrive init)

/-- A general schedule of micro-ops, for the Plausible sweep. -/
inductive Op | rx | post | iter
  deriving Repr, DecidableEq

def step (post iterf : St → St) (s : St) : Op → St
  | .rx => rxArrive s
  | .post => post s
  | .iter => iterf s

def run (post iterf : St → St) (ops : List Op) : St :=
  ops.foldl (step post iterf) init

def opOf (n : Nat) : Op := match n % 3 with | 0 => .rx | 1 => .post | _ => .iter
def sched (ns : List Nat) : List Op := ns.map opOf

/-- Inbound is being serviced: everything that arrived has been processed and
    nothing is stuck waiting. (For the coalesced loop this holds whenever the loop
    has had a chance to run; for the raw loop a wake flood keeps rxq pinned > 0.) -/
def inboundDrained (s : St) : Bool := s.rxq == 0

end Http3Queue.WakeLoop
