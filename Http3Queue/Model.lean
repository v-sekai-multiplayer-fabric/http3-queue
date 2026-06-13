namespace Http3Queue

/-- A model of the WebTransport/http3 server's inbound packet queue, the one that
    starves the 4th session. The Godot-side `List<IncomingPacket> incoming` is
    written by the picoquic network thread (`_push_wt_incoming_datagram`) and read
    by the main thread (`get_packet`/`get_available_packet_count`) with NO lock,
    while the outbound `WorkQueue` is mutex-protected. A `Godot::List` caches its
    length; the unguarded read-modify-write on that cached `size` (and the head
    links) is a classic lost update. When `size` is committed by a stale writer it
    drops below the true node count, so those nodes never surface through
    `get_available_packet_count()` — the newest session's packets are stranded.

    We model the shared list as `(nodes, size)`: `nodes` is the true content and
    `size` is the cached counter the reader trusts. A push or a pop each LOADs the
    current `size`, then later STOREs a value derived from its own snapshot. With
    the two threads interleaved (the racy semantics) a store can clobber the
    other's, so `size` diverges from `nodes.length`. With a lock (the fix) load and
    store are fused into one atomic op and the two always agree.

    Plausible witnesses the race (a quiescent state with `size < nodes.length`, a
    stranded packet) and confirms the locked queue conserves every packet. -/

abbrev Pkt := Nat   -- a packet, tagged by its session id

structure St where
  nodes  : List Pkt          -- the true list contents (head = front)
  size   : Nat               -- the cached length the reader trusts
  toPush : List Pkt          -- packets the producer still has to enqueue, in order
  pSnap  : Option (Nat × Pkt) -- producer mid-op: loaded `size`, will append this Pkt
  cSnap  : Option Nat        -- consumer mid-op: loaded `size`
  popped : List Pkt          -- packets the consumer has successfully delivered
  deriving Repr, DecidableEq

def init (ps : List Pkt) : St :=
  { nodes := [], size := 0, toPush := ps, pSnap := none, cSnap := none, popped := [] }

/-- A quiescent state has no thread mid-operation. -/
def quiescent (s : St) : Bool := s.pSnap.isNone && s.cSnap.isNone

/-- The four micro-steps of the UNLOCKED queue: each thread's load and store are
    distinct scheduler points, so they can interleave. -/
inductive Op | pLoad | pStore | cLoad | cStore
  deriving Repr, DecidableEq

/-- Unlocked semantics: last writer wins on `size` (the lost update). -/
def stepU (s : St) : Op → St
  | .pLoad =>
    -- producer loads the current size and grabs the next packet (one op in flight)
    match s.pSnap, s.toPush with
    | none, p :: rest => { s with pSnap := some (s.size, p), toPush := rest }
    | _, _ => s
  | .pStore =>
    -- producer commits: appends its packet and writes size := loaded+1
    match s.pSnap with
    | some (sz, p) => { s with nodes := s.nodes ++ [p], size := sz + 1, pSnap := none }
    | none => s
  | .cLoad =>
    match s.cSnap with
    | none => { s with cSnap := some s.size }
    | some _ => s
  | .cStore =>
    -- consumer commits: if it saw a non-empty queue, pop the head and write size := loaded-1
    match s.cSnap with
    | some sz =>
      if sz > 0 then
        match s.nodes with
        | h :: t => { s with nodes := t, popped := s.popped ++ [h], size := sz - 1, cSnap := none }
        | [] => { s with cSnap := none }            -- size said non-empty but nodes drained: nothing to take
      else { s with cSnap := none }                 -- saw empty: early return, no write
    | none => s

def runU (ps : List Pkt) (sched : List Op) : St :=
  sched.foldl stepU (init ps)

/-- The LOCKED queue (the fix): push and pop are each one atomic op, so the cached
    size and the contents can never disagree. -/
inductive OpL | push | pop
  deriving Repr, DecidableEq

def stepL (s : St) : OpL → St
  | .push =>
    match s.toPush with
    | p :: rest => { s with nodes := s.nodes ++ [p], size := s.size + 1, toPush := rest }
    | [] => s
  | .pop =>
    -- under the lock, `is_empty()`/`size`/`nodes` are consistent, so popping when
    -- the list is non-empty and decrementing size is one atomic act.
    match s.nodes with
    | h :: t => { s with nodes := t, popped := s.popped ++ [h], size := s.size - 1 }
    | [] => s

def runL (ps : List Pkt) (sched : List OpL) : St :=
  sched.foldl stepL (init ps)

/-- The queue's core invariant: the trusted `size` equals the real node count.
    When it fails with `size < nodes.length`, `get_available_packet_count()`
    under-reports and the extra nodes are stranded — the starvation. -/
def sizeHonest (s : St) : Bool := s.size == s.nodes.length

/-- Conservation: every packet taken from `toPush` is still somewhere we can
    account for it (delivered, in the queue, or in the producer's hand). A stranded
    packet sits in `nodes` but is invisible because `size` under-counts, so it is
    NOT accounted as deliverable. `accountable` counts only what the reader can
    still reach: the first `size` nodes plus delivered plus the in-flight push. -/
def reachable (s : St) : Nat := min s.size s.nodes.length

def accountedFor (s : St) : Nat :=
  reachable s + s.popped.length + (if s.pSnap.isSome then 1 else 0)

def taken (ps : List Pkt) (s : St) : Nat := ps.length - s.toPush.length

/-- No packet is lost: everything removed from the producer's input is still
    reachable, delivered, or in flight. -/
def noLoss (ps : List Pkt) (s : St) : Bool := accountedFor s == taken ps s

/-- Convert a numeric seed into an unlocked schedule (for the Plausible sweep). -/
def opOf (n : Nat) : Op :=
  match n % 4 with | 0 => .pLoad | 1 => .pStore | 2 => .cLoad | _ => .cStore

def schedU (ns : List Nat) : List Op := ns.map opOf

def opLOf (n : Nat) : OpL := if n % 2 == 0 then .push else .pop
def schedL (ns : List Nat) : List OpL := ns.map opLOf

end Http3Queue
