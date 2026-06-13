import Http3Queue
import Plausible
open Http3Queue Plausible

/- The inbound queue contract, checked two ways: the unlocked queue (today's bug)
   loses packets under a concurrent schedule; the locked queue (the fix) never
   does. The locked guarantee is also a proof, not just a sweep. -/

/-- THE FIX, proven. One atomic op per push/pop keeps the cached `size` exactly
    equal to the real node count, so `get_available_packet_count()` never
    under-reports and no packet is ever stranded. -/
theorem stepL_honest {s : St} {op : OpL} (h : s.size = s.nodes.length) :
    (stepL s op).size = (stepL s op).nodes.length := by
  cases op with
  | push =>
    cases ht : s.toPush with
    | nil => simp [stepL, ht, h]
    | cons p rest => simp [stepL, ht, List.length_append, h]
  | pop =>
    cases hn : s.nodes with
    | nil => simp [stepL, hn, h]
    | cons hh tt => simp only [stepL, hn, List.length_cons] at h ⊢; omega

theorem foldl_honest (sched : List OpL) :
    ∀ s, s.size = s.nodes.length →
      (sched.foldl stepL s).size = (sched.foldl stepL s).nodes.length := by
  induction sched with
  | nil => intro s h; simpa using h
  | cons op rest ih => intro s h; simp only [List.foldl_cons]; exact ih _ (stepL_honest h)

/-- For ANY producer input and ANY interleaving, the LOCKED queue keeps size
    honest — the structural reason no packet is stranded. -/
theorem runL_size_honest (ps : List Pkt) (sched : List OpL) :
    (runL ps sched).size = (runL ps sched).nodes.length :=
  foldl_honest sched (init ps) (by simp [init])

theorem runL_sizeHonest (ps : List Pkt) (sched : List OpL) :
    sizeHonest (runL ps sched) = true := by
  simp [sizeHonest, runL_size_honest]

-- Plausible sweeps of the LOCKED queue: size honest and no packet lost, always.
#eval Testable.check (∀ ns : List Nat, sizeHonest (runL [1,2,3] (schedL ns)) = true)
#eval Testable.check (∀ ns : List Nat, noLoss [1,2,3] (runL [1,2,3] (schedL ns)) = true)

-- The UNLOCKED queue is NOT honest. Plausible finds a quiescent schedule whose
-- cached size is below the true node count — a stranded packet — e.g.
--   ns := [0, 1, 6, 0, 3, 1]   (found in <16 shrinks)
-- A top-level `#eval Testable.check` of that universal exits non-zero by design
-- (it FOUND a counter-example), so we exhibit the same falsification at runtime in
-- `main` instead, keeping this a clean build alongside the proof of the fix.

/-- A concrete, hand-built interleaving that strands a packet, mirroring
    push_back(2) racing pop_front on the unlocked `incoming` list. -/
def witnessSched : List Op := [.pLoad, .pStore, .pLoad, .cLoad, .pStore, .cStore]

/- ===== The network-thread wake-flood wedge (the deep stall) ===== -/

/-- THE FIX, proven: a woken iteration still drains the socket, so inbound is
    serviced every iteration no matter what the wake pipe is doing — no wake stream
    can starve receive. (`iterIncl` always zeroes `rxq`.) -/
theorem iterIncl_drains (s : WakeLoop.St) : (WakeLoop.iterIncl s).rxq = 0 := by
  simp [WakeLoop.iterIncl]

/-- For the FIXED loop, after ANY schedule, one iteration leaves no inbound stuck:
    receive can never be starved by wake-ups. -/
theorem fixed_no_starvation (post : WakeLoop.St → WakeLoop.St) (ops : List WakeLoop.Op) :
    (WakeLoop.run post WakeLoop.iterIncl (ops ++ [WakeLoop.Op.iter])).rxq = 0 := by
  simp only [WakeLoop.run, List.foldl_append, List.foldl_cons, List.foldl_nil,
    WakeLoop.step, WakeLoop.iterIncl]

-- Plausible: the FIXED loop never strands inbound after a final iteration.
#eval Testable.check (∀ ns : List Nat,
  WakeLoop.inboundDrained (WakeLoop.run WakeLoop.postWakeRaw WakeLoop.iterIncl
    (WakeLoop.sched ns ++ [WakeLoop.Op.iter])) = true)

-- The BUGGY loop starves: under the adversarial "wake before every iteration"
-- load, inbound is NEVER received however long the loop runs — the wedge. The
-- FIXED loop receives it on the first iteration. (#guard checks both at compile.)
#guard (WakeLoop.runAdversarial WakeLoop.postWakeRaw WakeLoop.iterExcl 50).rcvd == 0
#guard (WakeLoop.runAdversarial WakeLoop.postWakeRaw WakeLoop.iterExcl 50).rxq == 1
#guard (WakeLoop.runAdversarial WakeLoop.postWakeRaw WakeLoop.iterIncl 50).rcvd == 1
#guard (WakeLoop.runAdversarial WakeLoop.postWakeRaw WakeLoop.iterIncl 50).rxq == 0

def main : IO Unit := do
  -- the locked fix: sweep size-honesty and conservation
  let mut badH := 0; let mut badL := 0
  for n in [0:30000] do
    let ns := (List.range (n % 13)).map (fun i => (n / (i+1) + i*5))
    if !(sizeHonest (runL [1,2,3] (schedL ns))) then badH := badH + 1
    if !(noLoss [1,2,3] (runL [1,2,3] (schedL ns))) then badL := badL + 1
  IO.println s!"LOCKED (fix): size-honest {30000 - badH}/30000, no-loss {30000 - badL}/30000"

  -- the bug: a concrete stranding witness on the unlocked queue
  let w := runU [1, 2] witnessSched
  IO.println s!"UNLOCKED witness {repr witnessSched}"
  IO.println s!"  -> nodes={w.nodes} size={w.size} popped={w.popped} quiescent={quiescent w}"
  IO.println s!"  -> size-honest={sizeHonest w} (size {w.size} vs nodes {w.nodes.length}); reachable={reachable w}, taken={taken [1,2] w}, no-loss={noLoss [1,2] w}"
  IO.println s!"  -> packet {w.nodes} is in the list but invisible: get_available_packet_count()={w.size} strands it."

  -- the wake-flood wedge: buggy (mutually-exclusive wake branch) vs fixed (inclusive)
  IO.println "WAKE-FLOOD wedge — adversarial 'wake before every iteration', 50 iters:"
  let wb := WakeLoop.runAdversarial WakeLoop.postWakeRaw WakeLoop.iterExcl 50
  let wf := WakeLoop.runAdversarial WakeLoop.postWakeRaw WakeLoop.iterIncl 50
  IO.println s!"  BUGGY (wake branch skips rx): rcvd={wb.rcvd} rxq={wb.rxq}  -> inbound STARVED forever"
  IO.println s!"  FIXED (woken iter still rx):   rcvd={wf.rcvd} rxq={wf.rxq}  -> inbound serviced"
  let mut starve := 0
  for n in [0:30000] do
    let ns := (List.range (3 + n % 9)).map (fun i => (n / (i+1) + i*2))
    if !(WakeLoop.inboundDrained (WakeLoop.run WakeLoop.postWakeRaw WakeLoop.iterExcl
          (WakeLoop.sched ns ++ [WakeLoop.Op.iter]))) then starve := starve + 1
  IO.println s!"  BUGGY sweep: {starve}/30000 schedules leave inbound stranded after a final iteration"

  -- runtime falsification sweep: how many random schedules strand a packet on the
  -- unlocked queue (quiescent yet size-dishonest)? — the bug is pervasive, not a fluke.
  let mut stranding := 0
  let mut firstWitness : Option (List Nat) := none
  for n in [0:30000] do
    let ns := (List.range (2 + n % 8)).map (fun i => (n / (i+1) + i*3))
    let s := runU [1,2,3] (schedU ns)
    if quiescent s && !(sizeHonest s) then
      stranding := stranding + 1
      if firstWitness.isNone then firstWitness := some ns
  IO.println s!"UNLOCKED sweep: {stranding}/30000 schedules strand a packet (quiescent but size<nodes)"
  match firstWitness with
  | some ns =>
      let s := runU [1,2,3] (schedU ns)
      IO.println s!"  first witness ns={ns} -> nodes={s.nodes} size={s.size} popped={s.popped} (no-loss={noLoss [1,2,3] s})"
  | none => IO.println "  (no stranding found — unexpected)"
