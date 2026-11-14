-- Generated current physical steps from signed c12 mem rows.
import DefaultRuntimeStepEvidence
import DefaultRuntimePhysicalRoutes
import PipeR14Mem.Physical.Steps_c12
import PipeR14.PinLink
import PipeR14.PlanChecks

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView ArmBridge.Boundary
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
namespace ReleaseProfile.DefaultRuntime
open PipeR14 PipeR14.Physical

#check "CURRENT_DECL step_c12_1"
theorem step_c12_1 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 1 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c12)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c12 regions_c12 sc base)
    (hp : PinsAgree p rs_c12 forms_c12 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 1 < capacity)
    (drawBound : past 1 + 1 ≤ past (1 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 19 (0))) false 4) 1 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 12) (by decide) rfl
    (c := (0x4, 0xb9400268)) (by decide) offset_c12 budget 1 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrWUoff.selected 8#5 19#5 0#12 = BitVec.ofNat 32 (0x4, 0xb9400268).2 := by decide
  obtain ⟨σf, hall⟩ := full_c12 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 19) = (extend inputs D_c12).getD 23 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = (extend inputs D_c12).getD 23 0 := hreg
  have hptr := ptr_c12_1 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 23 0 = BitVec.ofNat 64 (p.regs 19) := hp.1 19 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 19) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.LdrU32.addr x 19#5 0#12 = R14E17.dataVA p (.pin 19 (0)) := by
    unfold MemClass.LdrU32.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (0) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 19 (0), 4) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G19_c12.pin : Int) + G19_c12.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 19 (0)) + BitVec.ofNat 64 t := fun t => by
    simp only [G19_c12]; rw [pinv_of p 19 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 19 (0), 4) (by decide) G19_c12 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 4 → bytePA G19_c12 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU32.addr x 19#5 0#12) = some q → ∀ t : Nat, t < 4 → bytePA G19_c12 (0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have cov : ∀ ds σ, compileRun regions_c12 σ0_c12 inputs.length (plan_c12.take 1) = some (ds, σ) →
      ∀ t : Nat, t < 4 → ∃ i k', σ.memB G19_c12 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c12 σ0_c12 n0_c12 (plan_c12.take 1)).map
        (fun q => (List.range 4).all fun t => (q.2.memB G19_c12 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G19_c12 0 4 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU32.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table) 0#12 19#5 x := by
    unfold ArmCertMemPipe.LdrU32.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(1, .pin 19 (0), 4, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 19#5 0#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 19#5 0#12 1#2 2#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrWUoff.dispatch_at real pc 8#5 19#5 0#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU32.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c12 budget 1 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 19#5 0#12) 630 (by decide) 0#12 19#5 8#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c12 1 + 4#64 = offset_c12 2 by decide]) (hw ▸ ob) nodup bytePA regions_c12 G19_c12 0 lin [((.x 8), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c12 σ0_c12 inputs.length plan_c12).map Prod.fst = some D_c12 := by
    rw [hlen]
    exact compiles_D_c12
  have ok : (compileRun regions_c12 σ0_c12 inputs.length plan_c12).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 1) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c12_1

#check "CURRENT_DECL exit_c12"
theorem exit_c12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 5 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c12)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c12 regions_c12 sc base)
    (hp : PinsAgree p rs_c12 forms_c12 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 5 < capacity)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∀ x, ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past 5 x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ArmCertPipe.Physical.AgreesAt bytePA regions_c12 σ0_c12 inputs plan_c12 6 fin ∧
        fin.regs._PC = base + (offset_c12 5 + 4#64) ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
        ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 19 (0))) true 4) x fin ∧ (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 12) (by decide) rfl
    (c := (0x14, 0xb9000268)) (by decide) offset_c12 budget 5 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StrWUoff.selected 8#5 19#5 0#12 = BitVec.ofNat 32 (0x14, 0xb9000268).2 := by decide
  obtain ⟨σf, hall⟩ := full_c12 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 19) = (extend inputs D_c12).getD 23 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = (extend inputs D_c12).getD 23 0 := hreg
  have hptr := ptr_c12_5 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 23 0 = BitVec.ofNat 64 (p.regs 19) := hp.1 19 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 19) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.StrU32.addr x 19#5 0#12 = R14E17.dataVA p (.pin 19 (0)) := by
    unfold MemClass.StrU32.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (0) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 19 (0), 4) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G19_c12.pin : Int) + G19_c12.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 19 (0)) + BitVec.ofNat 64 t := fun t => by
    simp only [G19_c12]; rw [pinv_of p 19 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 19 (0), 4) (by decide) G19_c12 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 4 → bytePA G19_c12 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StrU32.addr x 19#5 0#12) = some q → ∀ t : Nat, t < 4 → bytePA G19_c12 (0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have facts : ArmCertMemPipe.StrU32.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c12) 0#12 19#5 x := by
    unfold ArmCertMemPipe.StrU32.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by rw [haddr]; exact align), (fun i hi => outside i hi), (fun i hi => ⟨(.pin 19 (0), 4), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(5, .pin 19 (0), 4, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StrWUoff.selected 8#5 19#5 0#12) (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 19#5 0#12 0#2 2#2) 648 := by
    intro pc t see; exact NativeEntryBodyDispatch.StrWUoff.dispatch_at real pc 8#5 19#5 0#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStrU32.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base (fun i => if i = 6 then offset_c12 5 + 4#64 else offset_c12 i) budget 5 catalogue room page (by decide) (NativeEntryBodyDispatch.StrWUoff.selected 8#5 19#5 0#12) 648 (by decide) 0#12 19#5 8#5 (by decide) (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c12) ds.code x (ReleaseProfile.DefaultRuntime.current_at_offset (offset := offset_c12) (offset' := (fun i => if i = 6 then offset_c12 5 + 4#64 else offset_c12 i)) (by simp) inv.core) (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc]; simp) (hw ▸ ob) nodup bytePA regions_c12 G19_c12 0 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 19 (0), 4)) (by decide) (r := G19_c12) (by decide) (n := 4) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_store32 bf) q' hq') [] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c12 σ0_c12 inputs.length plan_c12).map Prod.fst = some D_c12 := by
    rw [hlen]
    exact compiles_D_c12
  have ok : (compileRun regions_c12 σ0_c12 inputs.length plan_c12).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 5) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, next, by simpa using core.v1.pc, z, dit, ev, choice⟩

#print axioms exit_c12

end ReleaseProfile.DefaultRuntime
