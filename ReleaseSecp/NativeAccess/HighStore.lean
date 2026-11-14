import NativeAccess.StoreLoops
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace NativeAccess.HighStore
open NativeAccess.Trace NativeAccess.StoreLoops
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5 MemM1.MemWriteD6
attribute [local implicit_reducible] EStateM Arch.arch_ak
attribute [local irreducible] writeBody

theorem addInt_assoc (a : BitVec 64) (i j : Int) :
    BitVec.addInt (BitVec.addInt a i) j = BitVec.addInt a (i + j) := by
  simp [BitVec.addInt,BitVec.ofInt_add,BitVec.add_assoc]

theorem highBody (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128)
    (i : Nat) (bound : i < 8) (u : Unit) :
    writeBody (BitVec.addInt a 8) 8 acc false (Bytes.high64 value) (i : Int) u =
      writeBody a 16 acc false value ((8 + i : Nat) : Int) u := by
  unfold writeBody
  rw [Bytes.sail_byte_int _ _ (by omega),Bytes.sail_byte_int _ _ (by omega)]
  simp only [Int.toNat_natCast]
  rw [Bytes.high64_byte value i bound,addInt_assoc]
  congr 1

theorem highIterate (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128)
    (fuel start : Nat) (bound : start + fuel ≤ 8) (u : Unit) :
    Loops.iterate (writeBody (BitVec.addInt a 8) 8 acc false (Bytes.high64 value))
        fuel (start : Int) u =
      Loops.iterate (writeBody a 16 acc false value) fuel ((8 + start : Nat) : Int) u := by
  induction fuel generalizing start u with
  | zero => rfl
  | succ fuel ih =>
    simp only [Loops.iterate]
    rw [highBody a acc value start (by omega)]
    apply congrArg (fun f : Unit → SailM Unit => writeBody a 16 acc false value ((8 + start : Nat) : Int) u >>= f)
    funext next
    have left : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
    have right : ((8 + start : Nat) : Int) + 1 = ((8 + (start + 1) : Nat) : Int) := by omega
    rw [left,right]
    exact ih (start + 1) (by omega) next

#print axioms highIterate

theorem lowBody (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128)
    (i : Nat) (bound : i < 8) (u : Unit) :
    writeBody a 8 acc false (Bytes.low64 value) (i : Int) u =
      writeBody a 16 acc false value (i : Int) u := by
  unfold writeBody
  rw [Bytes.sail_byte_int _ _ (by omega),Bytes.sail_byte_int _ _ (by omega)]
  simp only [Int.toNat_natCast]
  rw [Bytes.low64_byte value i bound]

theorem iterate_congr_on (f g : Int → Unit → SailM Unit) (fuel start : Nat)
    (agree : ∀ i : Nat, start ≤ i → i < start + fuel → ∀ u, f (i : Int) u = g (i : Int) u)
    (u : Unit) : Loops.iterate f fuel (start : Int) u = Loops.iterate g fuel (start : Int) u := by
  induction fuel generalizing start u with
  | zero => rfl
  | succ fuel ih =>
    simp only [Loops.iterate]
    rw [agree start (by omega) (by omega)]
    apply congrArg (fun next : Unit → SailM Unit => g (start : Int) u >>= next)
    funext next
    have cursor : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
    rw [cursor]
    exact ih (start + 1) (fun i lo hi => agree i (by omega) (by omega)) next

theorem lowIterate (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128)
    (fuel start : Nat) (bound : start + fuel ≤ 8) (u : Unit) :
    Loops.iterate (writeBody a 8 acc false (Bytes.low64 value)) fuel (start : Int) u =
      Loops.iterate (writeBody a 16 acc false value) fuel (start : Int) u := by
  apply iterate_congr_on
  intro i lo hi next
  exact lowBody a acc value i (by omega) next

def highSuffix (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128) : SailM Unit := do
  let _ ← forIn ({start := 0,stop := 7,step := 1} : IntRange) ()
    (fun i u => do let next ← writeBody (BitVec.addInt a 8) 8 acc false (Bytes.high64 value) i u; pure (.yield next))
  forIn ({start := 0,stop := 7,step := 1} : IntRange) ()
    (fun i u => do let next ← writeBody a 8 acc false (Bytes.low64 value) i u; pure (.yield next))

theorem highPlan_eq (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128) :
    Logical.store16_highBytePlan a acc value = (do
      let value ← storePrefix a 16 acc value
      highSuffix a acc value) := by
  have half : Sail.Int.toNatChecked (Int.ediv (16 : Int) 2) = 8 := by decide
  have sixteen : ((16 : Nat) : Int) = 16 := by decide
  have eight : ((8 : Nat) : Int) = 8 := by decide
  have stop : (8 : Int) - 1 = 7 := by decide
  unfold Logical.store16_highBytePlan storePrefix
  simp only [sixteen,half,eight,stop]
  simp only [highSuffix,writeBody,Bytes.high64,Bytes.low64,bind_assoc,pure_bind,bind_pure]

theorem highSuffix_eq (a : BitVec 64) (acc : AccessDescriptor) (value : BitVec 128) :
    highSuffix a acc value = (do
      let _ ← Loops.iterate (writeBody a 16 acc false value) 8 8 ()
      Loops.iterate (writeBody a 16 acc false value) 8 0 ()) := by
  unfold highSuffix
  have highRange := Loops.range_eq_iterate (0 : Int) 8 ()
    (writeBody (BitVec.addInt a 8) 8 acc false (Bytes.high64 value))
  have lowRange := Loops.range_eq_iterate (0 : Int) 8 ()
    (writeBody a 8 acc false (Bytes.low64 value))
  have stop : (0 : Int) + ((8 : Nat) : Int) - 1 = 7 := by decide
  simp only [stop] at highRange lowRange
  have high := highIterate a acc value 8 0 (by omega) ()
  have low := lowIterate a acc value 8 0 (by omega) ()
  have zero : ((0 : Nat) : Int) = 0 := by decide
  have eight : ((8 + 0 : Nat) : Int) = 8 := by decide
  simp only [zero,eight] at high low
  rw [highRange,lowRange,high,low]

#print axioms highPlan_eq
#print axioms highSuffix_eq
theorem highPlan_run
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (value : BitVec (128)) (hA : AccDWT acc)
    (domains : Fin 16 → BitVec 64 → Prop)
    (specs : (j : Fin 16) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin 16 → AttributeConfig) (rows : Fin 16 → List PermissionRow)
    (mapping : Fin 16 → BitVec 64 → Option Nat) (pa : Fin 16 → BitVec 56)
    (mapped : ∀ j : Fin 16, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin 16, NotMMIO (pa j))
    (outside : ∀ j k : Fin 16, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (s : Trace.State)
    (host : HostPins s)
    (disabled : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (plain : Plain acc) (pre : PreW acc s.regs)
    (member : ∀ j : Fin 16, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin 16, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin 16, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin 16, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin 16, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin 16,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall),
      Logical.store16_highBytePlan a acc value s = .ok () after ∧ WriteChain s calls after ∧
      calls.map WriteCall.request =
        (List.range' 8 8).map (Loops.byteAccess offsetBase a acc false) ++
        (List.range' 0 8).map (Loops.byteAccess offsetBase a acc false) ∧
      ∀ call ∈ calls, ByteWitness offsetBase 0 16 a acc false value pa call := by
  rcases storePrefix_run a 16 acc value s host disabled plain hA pre with ⟨u,preRun,frame⟩
  have curU := fun j => current_s1_frame (current j) frame.1 frame.2.1
  have rawU : ∀ j : Fin 16, RawImageAt (specs j).imageRows u.mem := by
    intro j; rw [frame.2.1]; exact raw j
  rcases write_iterate (by decide) offsetBase a acc false value hA (fun j q => domains j q.va)
      specs configs rows mapping pa mapped ram outside 8 8 (by decide) u member data curU
      (fun j => (access j).of_regs frame.1)
      (by rw [frame.1]; exact mode) (by rw [frame.1]; exact aa64)
      (by rw [frame.1]; exact debug) (by rw [frame.1]; exact spe)
      (by rw [frame.1]; exact tag) (by rw [frame.1]; exact dcache) rawU
      (by intro j; rw [frame.1]; exact none j) with
    ⟨s1,highCalls,highRun,highChain,highRequests,highWitness⟩
  have preserved : ∀ k : Fin 16, CurrentS1At (specs k) (configs k) (rows k) s1 ∧
      RawImageAt (specs k).imageRows s1.mem := by
    intro k
    exact current_after_byteChain (curU k) (rawU k) highChain highWitness (fun j => outside j k)
  have regs : s1.regs = s.regs := highChain.registers.trans frame.1
  rcases write_iterate (by decide) offsetBase a acc false value hA (fun j q => domains j q.va)
      specs configs rows mapping pa mapped ram outside 0 8 (by decide) s1 member data
      (fun j => (preserved j).1) (fun j => (access j).of_regs regs)
      (by rw [regs]; exact mode) (by rw [regs]; exact aa64)
      (by rw [regs]; exact debug) (by rw [regs]; exact spe)
      (by rw [regs]; exact tag) (by rw [regs]; exact dcache)
      (fun j => (preserved j).2) (by intro j; rw [regs]; exact none j) with
    ⟨s2,lowCalls,lowRun,lowChain,lowRequests,lowWitness⟩
  refine ⟨s2,highCalls ++ lowCalls,?_,chain_prepend frame (chain_append highChain lowChain),?_,?_⟩
  · have eight : ((8 : Nat) : Int) = 8 := by decide
    have zero : ((0 : Nat) : Int) = 0 := by decide
    simp only [eight] at highRun
    simp only [zero] at lowRun
    rw [highPlan_eq]
    simp only [Bind.bind,EStateM.bind,preRun]
    rw [highSuffix_eq]
    simp only [Bind.bind,EStateM.bind,highRun,lowRun]
  · rw [List.map_append,highRequests,lowRequests]
  · intro call memberCall
    rcases List.mem_append.mp memberCall with high | low
    · obtain ⟨j,lo,hi,request,physical,payload⟩ := highWitness call high
      exact ⟨j,by omega,by omega,request,physical,payload⟩
    · obtain ⟨j,lo,hi,request,physical,payload⟩ := lowWitness call low
      exact ⟨j,by omega,by omega,request,physical,payload⟩

#print axioms highPlan_run
theorem store16_bytes_high
    (offsetBase : Nat) (a : BitVec 64) (acc : AccessDescriptor)
    (unaligned : IsAligned__1 a ((8 : Nat) : Int) = false)
    (value : BitVec (128)) (hA : AccDWT acc)
    (domains : Fin 16 → BitVec 64 → Prop)
    (specs : (j : Fin 16) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin 16 → AttributeConfig) (rows : Fin 16 → List PermissionRow)
    (mapping : Fin 16 → BitVec 64 → Option Nat) (pa : Fin 16 → BitVec 56)
    (mapped : ∀ j : Fin 16, mapping j (BitVec.addInt a (j.val : Int)) = some (pa j).toNat)
    (ram : ∀ j : Fin 16, NotMMIO (pa j))
    (outside : ∀ j k : Fin 16, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (s : Trace.State)
    (profile : AccessProfile) (pins : ProfileAt profile s) (lrcpc3 : profile.lrcpc3 = true)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) 16 == Align_bits a 16)) = false)
    (plain : Plain acc) (pre : PreW acc s.regs)
    (member : ∀ j : Fin 16, domains j (BitVec.addInt a (j.val : Int)))
    (data : ∀ j : Fin 16, S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery a acc false j.val))
    (current : ∀ j : Fin 16, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin 16, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      (Loops.byteQuery a acc false j.val) (data j) s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (tag : TagOK acc s.regs) (dcache : currentDCache s.regs = true)
    (raw : ∀ j : Fin 16, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin 16,
      NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true) :
    ∃ (after : Trace.State) (calls : List WriteCall),
      Mem_set__2 a 16 acc true true value s = .ok () after ∧ WriteChain s calls after ∧
      calls.map WriteCall.request =
        (List.range' 8 8).map (Loops.byteAccess offsetBase a acc false) ++
        (List.range' 0 8).map (Loops.byteAccess offsetBase a acc false) ∧
      ∀ call ∈ calls, ByteWitness offsetBase 0 16 a acc false value pa call := by
  rcases highPlan_run offsetBase a acc value hA domains specs configs rows mapping pa
      mapped ram outside s pins.host pins.alignment_disabled plain pre member data current access mode aa64
      debug spe tag dcache raw none with ⟨after,calls,run,chain,requests,witness⟩
  refine ⟨after,calls,?_,chain,requests,witness⟩
  rw [Logical.store16_bytes_high a unaligned acc hA plain value s profile pins lrcpc3 pre notJoin]
  exact run

#print axioms store16_bytes_high
end NativeAccess.HighStore
