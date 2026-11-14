import NativeAccess.Current
import NativeAccess.Bytes
import NativeAccess.Logical
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local implicit_reducible] EStateM Arch.arch_ak
namespace NativeAccess.Loops
abbrev State := SequentialState Regs oracleChoiceSource
open NativeAccess.Trace
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2

def iterate {β : Type} (body : Int → β → SailM β) : Nat → Int → β → SailM β
  | 0, _, value => pure value
  | n + 1, i, value => do
    let next ← body i value
    iterate body n (i + 1) next

theorem mem_step_one (range : IntRange) (step : range.step = 1) (i : Int) :
    i ∈ range ↔ range.start ≤ i ∧ i ≤ range.stop := by
  simp [Membership.mem,IntRange.instMemIntRange,step]

theorem loop_eq_iterate {β : Type} (range : IntRange) (step : range.step = 1)
    (body : Int → β → SailM β) (n : Nat) (i : Int) (value : β)
    (lower : range.start ≤ i) (last : range.stop = i + (n : Int) - 1)
    (stride : (i - range.start) % range.step = 0) :
    IntRange.forIn'.loop range (fun j _ x => do let y ← body j x; pure (.yield y)) value i stride =
      iterate body n i value := by
  induction n generalizing i value with
  | zero =>
    have outside : ¬ i ∈ range := by rw [mem_step_one range step]; omega
    rw [IntRange.forIn'.loop]
    simp only [dif_neg outside,iterate]
  | succ n ih =>
    have inside : i ∈ range := by rw [mem_step_one range step]; constructor <;> omega
    rw [IntRange.forIn'.loop]
    simp only [dif_pos inside,bind_assoc,pure_bind,step,iterate]
    apply congrArg (fun f : β → SailM β => body i value >>= f)
    funext next
    apply ih <;> omega

theorem range_eq_iterate {β : Type} (start : Int) (n : Nat) (value : β)
    (body : Int → β → SailM β) :
    forIn ({ start := start, stop := start + (n : Int) - 1, step := 1 } : IntRange) value
      (fun i x => do let y ← body i x; pure (.yield y)) = iterate body n start value := by
  change IntRange.forIn'.loop { start := start, stop := start + (n : Int) - 1, step := 1 }
    (fun i _ x => do let y ← body i x; pure (.yield y)) value start _ = _
  apply loop_eq_iterate <;> first | rfl | (dsimp; omega)

def readBody (a : BitVec 64) (n : Nat) (acc : AccessDescriptor) (aligned : Bool)
    (i : Int) (value : BitVec (n * 8)) : SailM (BitVec (n * 8)) := do
  let byte ← AArch64_MemSingle_read (BitVec.addInt a i) 1 acc aligned
  pure (Sail.BitVec.updateSubrange value (Sail.Int.toNatChecked (8 * i + 7))
    (Sail.Int.toNatChecked (8 * i)) (Sail.BitVec.castWidth byte))

def byteAccess (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (i : Nat) :
    Trace.Access := ⟨offsetBase + i,BitVec.addInt a (i : Int),1,acc,aligned,false⟩

def byteQuery (a : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (i : Nat) : AccessQuery :=
  ⟨BitVec.addInt a (i : Int),⟨acc,aligned⟩,((1 : Nat) : Int)⟩

/-- Finite, state-local query facts are consumed only at actual iteration
indices. Every later state's current facts are derived after the preceding
actual read. No state-universal caller readiness/coherence premise occurs. -/
theorem read_iterate {N : Nat} (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned : Bool)
    (initial target : BitVec (N * 8)) (hA : AccDR2 acc)
    (domains : Fin N → QueryDomain) (specs : (j : Fin N) → TopologyImageSpec (domains j))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (start fuel : Nat) (bounded : start + fuel ≤ N) (s : State)
    (member : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel → domains j (byteQuery a acc aligned j.val))
    (data : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      S1AccessData (specs j) (configs j) (rows j) (byteQuery a acc aligned j.val))
    (current : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ (j : Fin N) (lo : start ≤ j.val) (hi : j.val < start + fuel),
      CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
        (byteQuery a acc aligned j.val) (data j lo hi) s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel → RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true)
    (bytes : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      s.mem[(pa j).toNat]? = some (target.extractLsb' (8 * j.val) 8)) :
    ∃ (after : State) (calls : List ReadCall),
      iterate (readBody a N acc aligned) fuel (start : Int) (Bytes.fill initial target start) s =
        .ok (Bytes.fill initial target (start + fuel)) after ∧
      ReadChain s calls after ∧
      calls.map ReadCall.request = (List.range' start fuel).map (byteAccess offsetBase a acc aligned) := by
  induction fuel generalizing start s with
  | zero =>
    exact ⟨s,[],rfl,ReadChain.nil ⟨rfl,rfl,rfl⟩,rfl⟩
  | succ fuel ih =>
    let j : Fin N := ⟨start,by omega⟩
    have lo : start ≤ j.val := by dsimp [j]; omega
    have hi : j.val < start + (fuel + 1) := by dsimp [j]; omega
    rcases Current.read_byte (specs j) (configs j) (rows j) (mapping j)
        (offsetBase + start) (BitVec.addInt a (start : Int)) acc aligned false s
        (member j lo hi) (data j lo hi) (current j lo hi) (access j lo hi)
        mode debug post hA dcache (pa j) (mapped j) (ram j) (raw j lo hi) (none j lo hi)
        (target.extractLsb' (8 * start) 8)
        (by
          intro k hk
          have k0 : k = 0 := by omega
          subst k
          simpa only [Nat.mul_zero,Nat.add_zero,BitVec.extractLsb'_eq_self] using bytes j lo hi) with
      ⟨packet,value⟩
    have wrapper := Current.read_wrapper packet rfl
    change AArch64_MemSingle_read (BitVec.addInt a (start : Int)) 1 acc aligned s =
      .ok packet.data packet.after at wrapper
    rw [value] at wrapper
    have first : readBody a N acc aligned (start : Int) (Bytes.fill initial target start) s =
        .ok (Bytes.fill initial target (start + 1)) packet.after := by
      simp only [readBody,Bind.bind,EStateM.bind,wrapper,Pure.pure,EStateM.pure]
      rw [Bytes.sail_setByte_indices]
      rfl
    have rest := ih (start := start + 1) (s := packet.after) (bounded := by omega)
      (member := fun k low high => member k (by omega) (by omega))
      (data := fun k low high => data k (by omega) (by omega))
      (current := fun k low high => current_s1_frame (current k (by omega) (by omega))
        packet.registers packet.memory)
      (access := fun k low high => (access k (by omega) (by omega)).of_regs packet.registers)
      (mode := by rw [packet.registers]; exact mode)
      (debug := by rw [packet.registers]; exact debug)
      (post := by rw [packet.registers]; exact post)
      (dcache := by rw [packet.registers]; exact dcache)
      (raw := by intro k low high; rw [packet.memory]; exact raw k (by omega) (by omega))
      (none := by intro k low high; rw [packet.registers]; exact none k (by omega) (by omega))
      (bytes := by intro k low high; rw [packet.memory]; exact bytes k (by omega) (by omega))
    rcases rest with ⟨after,calls,run,chain,requests⟩
    let call : ReadCall := ⟨byteAccess offsetBase a acc aligned start,s,packet⟩
    refine ⟨after,call :: calls,?_,ReadChain.cons call ⟨rfl,rfl,rfl⟩ chain,?_⟩
    · have cursor : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
      have index : start + 1 + fuel = start + (fuel + 1) := by omega
      simp only [iterate,Bind.bind,EStateM.bind,first,cursor,run,index]
    · change byteAccess offsetBase a acc aligned start :: calls.map ReadCall.request = _
      rw [List.range'_succ,List.map_cons,requests]

theorem read_range {N : Nat} (small : N ≤ 16)
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor) (aligned : Bool)
    (initial target : BitVec (N * 8)) (hA : AccDR2 acc)
    (domains : Fin N → QueryDomain) (specs : (j : Fin N) → TopologyImageSpec (domains j))
    (configs : Fin N → AttributeConfig) (rows : Fin N → List PermissionRow)
    (mapping : Fin N → BitVec 64 → Option Nat) (pa : Fin N → BitVec 56)
    (mapped : ∀ j : Fin N, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin N, NotMMIO (pa j))
    (start fuel : Nat) (bounded : start + fuel ≤ N) (s : State)
    (member : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel → domains j (byteQuery a acc aligned j.val))
    (data : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      S1AccessData (specs j) (configs j) (rows j) (byteQuery a acc aligned j.val))
    (current : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ (j : Fin N) (lo : start ≤ j.val) (hi : j.val < start + fuel),
      CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
        (byteQuery a acc aligned j.val) (data j lo hi) s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel → RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true)
    (bytes : ∀ j : Fin N, start ≤ j.val → j.val < start + fuel →
      s.mem[(pa j).toNat]? = some (target.extractLsb' (8 * j.val) 8)) :
    ∃ (after : State) (calls : List ReadCall),
      (forIn ({start := (start : Int),stop := (start : Int) + (fuel : Int) - 1,step := 1} : IntRange)
        (Bytes.fill initial target start)
        (fun i word => do let next ← readBody a N acc aligned i word; pure (.yield next)) : SailM _) s =
        .ok (Bytes.fill initial target (start + fuel)) after ∧
      ReadChain s calls after ∧
      calls.map ReadCall.request = (List.range' start fuel).map (byteAccess offsetBase a acc aligned) := by
  rcases read_iterate small offsetBase a acc aligned initial target hA domains specs configs rows mapping pa
      mapped ram start fuel bounded s member data current access mode debug post dcache raw none bytes with
    ⟨after,calls,run,chain,requests⟩
  refine ⟨after,calls,?_,chain,requests⟩
  rw [range_eq_iterate]
  exact run

/-- Effect chains retain past choice/control frames without requiring full
state identity. The actual enclosing run must derive those frames. -/
theorem readChain_prepend {s u t : State} {calls : List ReadCall}
    (frame : Frame s u) (chain : ReadChain u calls t) : ReadChain s calls t := by
  cases chain with
  | nil f => exact .nil (frame_trans frame f)
  | cons c f tail => exact .cons c (frame_trans frame f) tail

theorem readChain_append {s u t : State} {left right : List ReadCall}
    (first : ReadChain s left u) (second : ReadChain u right t) : ReadChain s (left ++ right) t := by
  induction first with
  | nil f => exact readChain_prepend f second
  | cons c f tail ih => exact .cons c f (ih second)

theorem readChain_before {s t : State} {calls : List ReadCall} (chain : ReadChain s calls t)
    (call : ReadCall) (member : call ∈ calls) : call.before.regs = s.regs ∧ call.before.mem = s.mem := by
  induction chain with
  | nil f => cases member
  | cons c f tail ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨f.1,f.2.1⟩
    · obtain ⟨regs,mem⟩ := ih inside
      exact ⟨regs.trans (c.packet.registers.trans f.1),mem.trans (c.packet.memory.trans f.2.1)⟩

#print axioms read_range
#print axioms readChain_before
#print axioms read_iterate
#print axioms range_eq_iterate
#print axioms loop_eq_iterate
end NativeAccess.Loops
