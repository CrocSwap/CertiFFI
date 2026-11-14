import Bridge.CruxGenGuarded.EvSteps.CT
import Bridge.CruxGenGuarded.ConsumerMapShim
import HeapV2StepCerts.Residue.RAssembly
import HeapV2StepCerts.Residue.ZRun
import RtDit.DitBody
import HeapV2StepCerts.DataRecs
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace ArmBridge.CruxGenGuarded.Release
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! RELEASE HEADLINE SKELETON, GENERIC over
the deployment (spec, config, rows, mapping, load base, pins). The run starts at the caller's BL
into the shim (state 0 = shim entry, index j of `stateAt real e`): shim prologue s0..s6 = 0..6,
body steps k = 0..357 at 7..364 (the body's final RET lands at 365 = shim s7), shim epilogue
s7..s10 = 365..368, caller return point = 369.

PROVED here (composed from compiled theorems): E17 on the body (e17_general), CT0 on the body
(ct_general), DIT constant through the body (dit_body), the body frame residue (ct2Residue_run),
and the composition of all of them with the shim parts along ONE actual run.

NAMED HYPOTHESES (the remaining work; each owner's "done" = discharging its hypothesis):
* `ShimPrologue` / `ShimEpilogue` (H-P13): discharged by shim_release_v2 into its
  instance premises (see GuardedReleaseInst.release_normal_inst).
* `ShimKeep` (H-P13k, /): frameRegs, X19 and _Z unchanged across the shim steps.
* `Functional`: O = I^2 mod p, x0 = 0.
N/C/V (B1b), V8..V15, the scrub and Z are proved (Memory's ct2Residue_full).
No sorry / axiom: the hypotheses are explicit theorem premises. -/

/-- The shim's public PC at shim index j (s0..s10 at shim offset + 4j). -/
def shimPC (j : Nat) : BitVec 64 := BitVec.ofNat 64 (0x10548 + 4 * j)

/-- The shim's data records: the 16-byte slot store at s3, the ISB barrier at s5 (
335b: EntryIsbSy appends Barrier_ISB), and the slot load at s7 (VA = body SP pin). -/
def shimData {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) (j : Nat) :
    List (Option ArmCertCTOrdered.OrderedEventV2.Record) :=
  if j = 3 then HeapV2StepCerts.DataRecs.dataRecs spec (BitVec.ofNat 64 pins.sp) true 16
  else if j = 5 then [ArmCertCTOrdered.OrderedEventV2.record (.barrier (.Barrier_ISB ()) : Event)]
  else if j = 7 then HeapV2StepCerts.DataRecs.dataRecs spec (BitVec.ofNat 64 pins.sp) false 16
  else []

/-- The shim map (shim code + slot + body accesses). -/
abbrev shimMap {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  HeapV2E17.consumerMapShim (fun _ => True) pins base.toNat mapping (rowsFootprint spec.imageRows).byte

/-- NAMED (H-P13): the shim prologue s0..s6 on the actual run from shim entry e. -/
structure ShimPrologue (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (budget : Nat) (e : NativeState) : Prop where
  steps : ∀ j, j < 7 → modelStep real (stateAt real e j) = .ok () (stateAt real e (j + 1))
  e17 : ∀ j, j ≤ 6 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (shimMap spec mapping base pins) (stateAt real e j)
  ev : ∀ j, j < 7 → StepEvents.EvShape spec mapping (shimData spec pins j) (stateAt real e j) (stateAt real e (j + 1))
  pc : ∀ j, j ≤ 6 → (stateAt real e j).regs._PC = base + shimPC j
  ditOn : ∀ j, 5 ≤ j → j ≤ 6 → (stateAt real e j).regs.PSTATE.DIT = 1#1
  body : ∀ e', e' = stateAt real e 7 → DeploymentPremises spec config rows mapping base pins e' budget
  qBody : qOf (stateAt real e 7) = qOf e
  ditBody : (stateAt real e 7).regs.PSTATE.DIT = 1#1

/-- NAMED (H-P13): the shim epilogue s7..s10 after the body's RET, and the exit. -/
structure ShimEpilogue (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins) (callerPC : BitVec 64)
    (e : NativeState) : Prop where
  steps : ∀ j, 364 ≤ j → j < 369 → modelStep real (stateAt real e j) = .ok () (stateAt real e (j + 1))
  e17 : ∀ j, 365 ≤ j → j ≤ 369 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (shimMap spec mapping base pins) (stateAt real e j)
  evRet : StepEvents.EvShape spec mapping [] (stateAt real e 364) (stateAt real e 365)
  ev : ∀ j, 365 ≤ j → j < 369 → StepEvents.EvShape spec mapping (shimData spec pins (j - 358)) (stateAt real e j) (stateAt real e (j + 1))
  pc : ∀ j, 365 ≤ j → j ≤ 368 → (stateAt real e j).regs._PC = base + shimPC (j - 358)
  exitPC : (stateAt real e 369).regs._PC = callerPC + 4#64
  ditOn : ∀ j, 365 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1
  ditRestored : (stateAt real e 368).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧ (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT
  frame : (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 ∧
    (stateAt real e 369).regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = e.regs.gpr[30]

/-- NAMED (H-P13k): the shim leaves the callee-saved frame registers, X19 and _Z untouched
across its prologue (s0..s6) and its epilogue (s7..s10). Kept apart from ShimPrologue/ShimEpilogue
so their existing producers (RtDit4.Release) are unchanged. -/
structure ShimKeep (real : Type) [Sail.SailReal real] (e : NativeState) : Prop where
  keepIn : (∀ r ∈ HeapV2StepCerts.Residue.frameRegs, HeapV2StepCerts.RegBind.regVal (stateAt real e 7) (.x r) =
      HeapV2StepCerts.RegBind.regVal e (.x r)) ∧
    (stateAt real e 7).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = e.regs.gpr[19] ∧
    (stateAt real e 7).regs._Z = e.regs._Z
  keepOut : (∀ r ∈ HeapV2StepCerts.Residue.frameRegs, HeapV2StepCerts.RegBind.regVal (stateAt real e 369) (.x r) =
      HeapV2StepCerts.RegBind.regVal (stateAt real e 364) (.x r)) ∧
    (stateAt real e 369).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] =
      (stateAt real e 364).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] ∧
    (stateAt real e 369).regs._Z = (stateAt real e 364).regs._Z

/-- N, C, V after the epilogue TST (B1b): PROVED from ct2Residue_full (Memory stepcerts-b1b-d163). -/
structure ResidueNCV (real : Type) [Sail.SailReal real] (e : NativeState) : Prop where
  nzcv : (stateAt real e 364).regs.PSTATE.N = 0#1 ∧ (stateAt real e 364).regs.PSTATE.C = 0#1 ∧
    (stateAt real e 364).regs.PSTATE.V = 0#1

/-- The secp256k1 field modulus (= CertiFFI.Kernels.Secp256k1.modulus). -/
def p256k1 : Nat := 2 ^ 256 - (2 ^ 32 + 977)

/-- Byte i of the 32-byte little-endian buffer at VA va, read through the mapping. -/
def bufByte (mapping : BitVec 64 → Option Nat) (s : NativeState) (va : Nat) (i : Nat) : Option (BitVec 8) :=
  (mapping (BitVec.ofNat 64 (va + i))).bind fun pa => s.mem[pa]?

/-- The 256-bit little-endian value of the input buffer I = [x1, x1+32) at entry. -/
def inputValue (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) (s : NativeState) : Nat :=
  (List.range 32).foldr (fun i acc => acc * 256 + ((bufByte mapping s pins.x1 i).getD 0#8).toNat) 0

/-- NAMED (H-P1): the functional result at the caller's return point: O[0,32) = I^2 mod p, x0 = 0. -/
def Functional (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) (e fin : NativeState) : Prop :=
  fin.regs.gpr[0] = 0#64 ∧
    ∀ i, i < 32 → bufByte mapping fin pins.x0 i =
      some (BitVec.ofNat 8 ((inputValue mapping pins e ^ 2 % p256k1) / 256 ^ i))

/-- E17 map at shim-run index j. -/
def mapAt {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (j : Nat) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  if 7 ≤ j ∧ j ≤ 364 then cmap spec mapping base pins else shimMap spec mapping base pins

theorem body_index (real : Type) [Sail.SailReal real] (e : NativeState) (k : Nat) :
    stateAt real e (7 + k) = stateAt real (stateAt real e 7) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (next real) ih

run_cmd do
  IO.eprintln "CURRENT_DECL Release.release_normal"
  (← IO.getStderr).flush

/-- RELEASE HEADLINE (single run, normal path), skeleton. -/
theorem release_normal (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (e : NativeState) (budget : Nat) (hb : 357 ≤ budget) (callerPC : BitVec 64)
    (normal : HeapV2StepCerts.ValBind.NormalPath pins (qOf e))
    (pro : ShimPrologue real spec config rows mapping base pins budget e)
    (epi : ShimEpilogue real spec mapping base pins callerPC e)
    (keep : ShimKeep real e)
    (func : Functional mapping pins e (stateAt real e 369)) :
    -- E17 at every state of the actual run
    (∀ j, j ≤ 369 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (mapAt spec mapping base pins j) (stateAt real e j)) ∧
    -- DIT window: DIT = 1 on [5, 367], caller DIT restored at 368/369
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
      (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
    -- exit at the caller's return point
    (stateAt real e 369).regs._PC = callerPC + 4#64 ∧
    -- body frame residue (ct2Residue_run at the body's RET) + its gaps + the shim frame
    -- ABI callee-saved / frame, relative to the CALLER's entry e: X18, X20..X29, X19, X30, SP, SIMD file
    ((∀ r ∈ HeapV2StepCerts.Residue.frameRegs, HeapV2StepCerts.RegBind.regVal (stateAt real e 369) (.x r) =
        HeapV2StepCerts.RegBind.regVal e (.x r)) ∧
      (stateAt real e 369).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = e.regs.gpr[19] ∧
      (stateAt real e 369).regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = e.regs.gpr[30] ∧
      (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 ∧
      (stateAt real e 369).regs._Z = e.regs._Z ∧
      (∀ a, ¬ HeapV2StepCerts.Residue.StoreBytes pins mapping a → (stateAt real e 364).mem[a]? = (stateAt real e 7).mem[a]?) ∧
      -- scrub (CT2): x0..x17 = 0 and NZCV at the body's end
      (∀ i : Fin 18, HeapV2StepCerts.RegBind.regVal (stateAt real e 364) (.x (Fin.castLE (by decide) i)) = 0#64) ∧
      (stateAt real e 364).regs.PSTATE.Z = 1#1 ∧ ResidueNCV real e) ∧
    -- functional result
    Functional mapping pins e (stateAt real e 369) := by
  have dp := pro.body _ rfl
  have hE := (e17_general real spec config rows mapping base pins (stateAt real e 7) budget dp hb).1
  have hD := RtDit.dit_body real spec config rows mapping base pins (stateAt real e 7) budget dp hb
  have hR := HeapV2StepCerts.Residue.Run.ct2Residue_run real spec config rows mapping base pins (stateAt real e 7) budget dp hb
  have hZ := HeapV2StepCerts.ZSteps.ct2Residue_full real spec config rows mapping base pins (stateAt real e 7) budget dp hb
  have i364 : stateAt real e 364 = stateAt real (stateAt real e 7) 357 := body_index real e 357
  refine ⟨?_, ?_, epi.ditRestored.2, epi.exitPC, ⟨?_, ?_, epi.frame.2, epi.frame.1, ?_, ?_, ?_, ?_, ?_⟩, func⟩
  · intro j hj
    by_cases lo : j ≤ 6
    · have hm : mapAt spec mapping base pins j = shimMap spec mapping base pins := by
        unfold mapAt; rw [if_neg (by omega)]
      rw [hm]; exact pro.e17 j lo
    by_cases hi : j ≤ 364
    · have hm : mapAt spec mapping base pins j = cmap spec mapping base pins := by
        unfold mapAt; rw [if_pos (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, j = 7 + k := ⟨j - 7, by omega⟩
      rw [hm, body_index]; exact (hE k (by omega)).2
    · have hm : mapAt spec mapping base pins j = shimMap spec mapping base pins := by
        unfold mapAt; rw [if_neg (by omega)]
      rw [hm]; exact epi.e17 j (by omega) hj
  · intro j lo hi
    by_cases a : j ≤ 6
    · exact pro.ditOn j lo a
    by_cases b : j ≤ 364
    · obtain ⟨k, rfl⟩ : ∃ k, j = 7 + k := ⟨j - 7, by omega⟩
      rw [body_index, hD k (by omega)]; exact pro.ditBody
    · exact epi.ditOn j (by omega) hi
  · intro r hr
    rw [keep.keepOut.1 r hr, i364, hZ.1 r hr]; exact keep.keepIn.1 r hr
  · rw [keep.keepOut.2.1, i364, hZ.2.2.1]; exact keep.keepIn.2.1
  · rw [keep.keepOut.2.2, i364, hZ.2.2.2.2.2.1]; exact keep.keepIn.2.2
  · intro a ha
    have := hR.2.2.2.2 a ha
    rw [show (364 : Nat) = 7 + 357 from rfl, body_index]; exact this
  · intro i; rw [i364]; exact hZ.2.2.2.2.2.2.1 i
  · rw [i364]; exact hZ.2.2.2.2.2.2.2.1
  · refine ⟨?_⟩; rw [i364]; exact ⟨hZ.2.2.2.2.2.2.2.2.1, hZ.2.2.2.2.2.2.2.2.2.1, hZ.2.2.2.2.2.2.2.2.2.2⟩

#print axioms release_normal

/-- Consecutive equal-shape steps at equal PCs compose to a TimingRec. -/
theorem seg_timing {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (d : Nat → List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (L R : Nat → NativeState) (a : Nat) :
    ∀ n, (∀ j, a ≤ j → j < a + n → StepEvents.EvShape spec mapping (d j) (L j) (L (j + 1)) ∧
        StepEvents.EvShape spec mapping (d j) (R j) (R (j + 1))) →
      (∀ j, a ≤ j → j ≤ a + n → (L j).regs._PC = (R j).regs._PC) →
      PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record (L a) (R a) (L (a + n)) (R (a + n)) := by
  intro n
  induction n with
  | zero => intro _ pc; exact PhasedCT.timing_refl _ _ _ (pc a (Nat.le_refl _) (by omega))
  | succ n ih =>
    intro ev pc
    have t := ih (fun j h1 h2 => ev j h1 (by omega)) (fun j h1 h2 => pc j h1 (by omega))
    have e := ev (a + n) (by omega) (by omega)
    exact PhasedCT.timing_trans _ _ _ _ _ _ _ t
      (StepEvents.pair spec mapping (d (a + n)) _ _ _ _ e.1 e.2 (pc (a + n) (by omega) (by omega))
        (pc (a + n + 1) (by omega) (by omega)))

/-- The data records at shim-run index j. -/
def runData {domain : QueryDomain} (spec : TopologyImageSpec domain) (pins : HeapV2E17.Pins) (j : Nat) :
    List (Option ArmCertCTOrdered.OrderedEventV2.Record) :=
  if j < 7 then shimData spec pins j else if j = 364 then [] else shimData spec pins (j - 358)

run_cmd do
  IO.eprintln "CURRENT_DECL Release.release_ct0"
  (← IO.getStderr).flush

/-- RELEASE HEADLINE CT0 (two runs, normal path), skeleton: two shim entries with the same
deployment, pins and caller return point (each with its own prologue/epilogue facts) produce
record-equal traces over the WHOLE shim + body run, 369 steps. -/
theorem release_ct0 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (el er : NativeState) (budget : Nat) (hb : 357 ≤ budget) (callerPC : BitVec 64)
    (prol : ShimPrologue real spec config rows mapping base pins budget el)
    (pror : ShimPrologue real spec config rows mapping base pins budget er)
    (epil : ShimEpilogue real spec mapping base pins callerPC el)
    (epir : ShimEpilogue real spec mapping base pins callerPC er) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record el er (stateAt real el 369) (stateAt real er 369) := by
  have dpl := prol.body _ rfl
  have dpr := pror.body _ rfl
  have hl := (e17_general real spec config rows mapping base pins (stateAt real el 7) budget dpl hb).1
  have hr := (e17_general real spec config rows mapping base pins (stateAt real er 7) budget dpr hb).1
  have bodyPC : ∀ k, k ≤ 357 → (stateAt real el (7 + k)).regs._PC = (stateAt real er (7 + k)).regs._PC := by
    intro k hk
    rw [body_index, body_index]
    exact (hl k hk).1.v3.v2.v1.pc.trans (hr k hk).1.v3.v2.v1.pc.symm
  -- prologue [0, 7)
  have t1 := seg_timing spec mapping (runData spec pins) (stateAt real el) (stateAt real er) 0 7
    (fun j _ h2 => by
      have hd : runData spec pins j = shimData spec pins j := by unfold runData; rw [if_pos (by omega)]
      rw [hd]; exact ⟨prol.ev j (by omega), pror.ev j (by omega)⟩)
    (fun j _ h2 => by
      by_cases h : j ≤ 6
      · rw [prol.pc j h, pror.pc j h]
      · obtain rfl : j = 7 := by omega
        exact bodyPC 0 (by omega))
  -- body [7, 364]
  have t2 : PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record (stateAt real el 7) (stateAt real er 7)
      (stateAt real el 364) (stateAt real er 364) := by
    have c := EvSteps.ct_general real spec config rows mapping base pins (stateAt real el 7) (stateAt real er 7)
      budget dpl dpr hb
    rw [show (364 : Nat) = 7 + 357 from rfl, body_index, body_index]; exact c
  -- epilogue [364, 369)
  have t3 := seg_timing spec mapping (runData spec pins) (stateAt real el) (stateAt real er) 364 5
    (fun j h1 h2 => by
      by_cases h : j = 364
      · subst h
        have hd : runData spec pins 364 = [] := by unfold runData; simp
        rw [hd]; exact ⟨epil.evRet, epir.evRet⟩
      · have hd : runData spec pins j = shimData spec pins (j - 358) := by
          unfold runData; rw [if_neg (by omega), if_neg h]
        rw [hd]; exact ⟨epil.ev j (by omega) (by omega), epir.ev j (by omega) (by omega)⟩)
    (fun j h1 h2 => by
      by_cases h : j = 364
      · subst h; exact bodyPC 357 (Nat.le_refl _)
      by_cases h' : j ≤ 368
      · rw [epil.pc j (by omega) h', epir.pc j (by omega) h']
      · obtain rfl : j = 369 := by omega
        rw [epil.exitPC, epir.exitPC])
  exact PhasedCT.timing_trans _ _ _ _ _ _ _ (PhasedCT.timing_trans _ _ _ _ _ _ _ t1 t2) t3

#print axioms release_ct0
end ArmBridge.CruxGenGuarded.Release
