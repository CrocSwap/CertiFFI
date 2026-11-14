-- Generated current physical steps from signed c05 mem rows.
import DefaultRuntimeStepEvidence
import DefaultRuntimePhysicalRoutes
import PipeR14Mem.Physical.Steps_c05
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

#check "CURRENT_DECL step_c05_0"
theorem step_c05_0 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 0 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 0 < capacity)
    (drawBound : past 0 + 1 ≤ past (0 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 16) 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x0, 0xa9be7bfd)) (by decide) offset_c05 budget 0 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StpPre.selected 29#5 30#5 124#7 = BitVec.ofNat 32 (0x0, 0xa9be7bfd).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c05).getD 72 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c05).getD 72 0 := hreg
  have hptr := ptr_c05_0 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 72 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.StpPre.ldpAddr x 124#7 = R14E17.dataVA p (.pin 31 (-32)) := by
    unfold MemClass.StpPre.ldpAddr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (-32) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-32), 16) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + 8 * (0 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-32), 16) (by decide) G31_c05 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 16 → bytePA G31_c05 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StpPre.ldpAddr x 124#7) = some q → ∀ t : Nat, t < 16 → bytePA G31_c05 (8 * 0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of0 _ ds.sp16
  have facts : ArmCertMemPipe.StpPre.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c05) 124#7 x := by
    unfold ArmCertMemPipe.StpPre.Facts; exact ⟨hsp16, (by rw [haddr]; exact align), pa, (by rw [haddr]; exact hmap), mmio, (fun i hi => outside i hi), (fun i hi => ⟨(.pin 31 (-32), 16), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(0, .pin 31 (-32), 16, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StpPre.selected 29#5 30#5 124#7) (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx 29#5 31#5 30#5 124#7 0#1 2#2) 616 := by
    intro pc t see; exact NativeEntryBodyDispatch.StpPre.dispatch_at real pc 29#5 30#5 124#7 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStpPre.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 0 catalogue room page (by decide) (NativeEntryBodyDispatch.StpPre.selected 29#5 30#5 124#7) 616 (by decide) 124#7 29#5 30#5 (by decide) (by decide) (-32) (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c05) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 0 + 4#64 = offset_c05 1 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G31_c05 0 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 31 (-32), 16)) (by decide) (r := G31_c05) (by decide) (n := 16) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_pair bf) q' hq') [(.sp, some ⟨.add, [.reg .sp, .lit 18446744073709551584#64]⟩)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 0) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_0

#check "CURRENT_DECL step_c05_1"
theorem step_c05_1 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 1 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 1 < capacity)
    (drawBound : past 1 + 1 ≤ past (1 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 8) 1 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x4, 0xf9000bf3)) (by decide) offset_c05 budget 1 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StrXUoffSP.selected 19#5 2#12 = BitVec.ofNat 32 (0x4, 0xf9000bf3).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c05).getD 77 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c05).getD 77 0 := hreg
  have hptr := ptr_c05_1 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 72 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffe0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : MemClass.StrU64Sp.addr x 2#12 = R14E17.dataVA p (.pin 31 (-16)) := by
    unfold MemClass.StrU64Sp.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK2 _ (-16) _ _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-16), 8) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + ((16 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + 8 * (2 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-16), 8) (by decide) G31_c05 (by decide) 16 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 8 → bytePA G31_c05 (16 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StrU64Sp.addr x 2#12) = some q → ∀ t : Nat, t < 8 → bytePA G31_c05 (8 * 2 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have facts : ArmCertMemPipe.StrU64Sp.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c05) 2#12 x := by
    unfold ArmCertMemPipe.StrU64Sp.Facts; exact ⟨hsp16, pa, (by rw [haddr]; exact hmap), mmio, (by rw [haddr]; exact align), (fun i hi => outside i hi), (fun i hi => ⟨(.pin 31 (-16), 8), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(1, .pin 31 (-16), 8, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StrXUoffSP.selected 19#5 2#12) (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 19#5 31#5 2#12 0#2 3#2) 648 := by
    intro pc t see; exact NativeEntryBodyDispatch.StrXUoffSP.dispatch_at real pc 19#5 2#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStrU64Sp.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 1 catalogue room page (by decide) (NativeEntryBodyDispatch.StrXUoffSP.selected 19#5 2#12) 648 (by decide) 2#12 19#5 (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c05) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 1 + 4#64 = offset_c05 2 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G31_c05 2 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 31 (-16), 8)) (by decide) (r := G31_c05) (by decide) (n := 8) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_store bf) q' hq') [] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 1) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_1

#check "CURRENT_DECL step_c05_5"
theorem step_c05_5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 5 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 5 < capacity)
    (drawBound : past 5 + 1 ≤ past (5 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (8))) false 8) 5 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x2c, 0xf9400409)) (by decide) offset_c05 budget 5 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrXUoff.selected 9#5 0#5 1#12 = BitVec.ofNat 32 (0x2c, 0xf9400409).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 0) = (extend inputs D_c05).getD 41 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (0#5 : BitVec 5).toNat).val] = (extend inputs D_c05).getD 41 0 := hreg
  have hptr := ptr_c05_5 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 41 0 = BitVec.ofNat 64 (p.regs 0) := hp.1 0 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (0#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 0) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.LdrU64.addr x 0#5 1#12 = R14E17.dataVA p (.pin 0 (8)) := by
    unfold MemClass.LdrU64.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (8) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 0 (8), 8) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G0_c05.pin : Int) + G0_c05.off + ((8 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 0 (8)) + BitVec.ofNat 64 t := fun t => by
    simp only [G0_c05]; rw [pinv_of p 0 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G0_c05.pin : Int) + G0_c05.off + 8 * (1 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 0 (8)) + BitVec.ofNat 64 t := fun t => by
    simp only [G0_c05]; rw [pinv_of p 0 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 0 (8), 8) (by decide) G0_c05 (by decide) 8 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 8 → bytePA G0_c05 (8 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU64.addr x 0#5 1#12) = some q → ∀ t : Nat, t < 8 → bytePA G0_c05 (8 * 1 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have cov : ∀ ds σ, compileRun regions_c05 σ0_c05 inputs.length (plan_c05.take 5) = some (ds, σ) →
      ∀ t : Nat, t < 8 → ∃ i k', σ.memB G0_c05 (8 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c05 σ0_c05 n0_c05 (plan_c05.take 5)).map
        (fun q => (List.range 8).all fun t => (q.2.memB G0_c05 (8 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G0_c05 8 8 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU64.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) 1#12 0#5 x := by
    unfold ArmCertMemPipe.LdrU64.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(5, .pin 0 (8), 8, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrXUoff.selected 9#5 0#5 1#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 9#5 0#5 1#12 1#2 3#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrXUoff.dispatch_at real pc 9#5 0#5 1#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU64.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 5 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrXUoff.selected 9#5 0#5 1#12) 630 (by decide) 1#12 0#5 9#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 5 + 4#64 = offset_c05 6 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G0_c05 1 lin [((.x 9), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 5) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_5

#check "CURRENT_DECL step_c05_10"
theorem step_c05_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 10 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 10 < capacity)
    (drawBound : past 10 + 1 ≤ past (10 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+UBFM64[1,63](x1)+24")) false 1) 10 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x40, 0x39406108)) (by decide) offset_c05 budget 10 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrbUoff.selected 8#5 8#5 24#12 = BitVec.ofNat 32 (0x40, 0x39406108).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 8) = (extend inputs D_c05).getD 85 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (8#5 : BitVec 5).toNat).val] = (extend inputs D_c05).getD 85 0 := hreg
  have hptr := ptr_c05_10 inputs (by rw [hlen]; rfl)
  have haddr : MemClass.LdrbU.addr x 8#5 24#12 = R14E17.dataVA p (.indirect "x0+UBFM64[1,63](x1)+24") := by
    unfold MemClass.LdrbU.addr; rw [hx, hptr]; simp only [R14E17.dataVA, R14E17.baseVA]
    rw [hp.2 "x0+UBFM64[1,63](x1)+24" (by decide), ofInt_toNat]
    simp only [formVal, op_add, op_lsr]
    rfl
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.indirect "x0+UBFM64[1,63](x1)+24", 1) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G33_c05.pin : Int) + G33_c05.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.indirect "x0+UBFM64[1,63](x1)+24") + BitVec.ofNat 64 t := fun t => by
    simp only [G33_c05]; rw [pinv_33]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.indirect "x0+UBFM64[1,63](x1)+24", 1) (by decide) G33_c05 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 1 → bytePA G33_c05 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrbU.addr x 8#5 24#12) = some q → bytePA G33_c05 0 = some q := by
    intro q hq; rw [haddr, hmap] at hq; cases hq; have := lin0 0 (by decide); simpa using this
  have cov : ∀ ds σ, compileRun regions_c05 σ0_c05 inputs.length (plan_c05.take 10) = some (ds, σ) →
      ∀ t : Nat, t < 1 → ∃ i k', σ.memB G33_c05 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c05 σ0_c05 n0_c05 (plan_c05.take 10)).map
        (fun q => (List.range 1).all fun t => (q.2.memB G33_c05 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G33_c05 0 1 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrbU.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) 24#12 8#5 x := by
    unfold ArmCertMemPipe.LdrbU.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), hbytes, (fun acc shape => Or.inl ⟨(10, .indirect "x0+UBFM64[1,63](x1)+24", 1, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrbUoff.selected 8#5 8#5 24#12) (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 8#5 24#12 1#2 0#2) 633 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrbUoff.dispatch_at real pc 8#5 8#5 24#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrbU.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 10 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrbUoff.selected 8#5 8#5 24#12) 633 (by decide) 24#12 8#5 8#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 10 + 4#64 = offset_c05 11 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G33_c05 0 lin [((.x 8), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 10) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_10

#check "CURRENT_DECL step_c05_13"
theorem step_c05_13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 13 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 13 < capacity)
    (drawBound : past 13 + 1 ≤ past (13 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4) 13 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x64, 0xb9400008)) (by decide) offset_c05 budget 13 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrWUoff.selected 8#5 0#5 0#12 = BitVec.ofNat 32 (0x64, 0xb9400008).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 0) = (extend inputs D_c05).getD 41 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (0#5 : BitVec 5).toNat).val] = (extend inputs D_c05).getD 41 0 := hreg
  have hptr := ptr_c05_13 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 41 0 = BitVec.ofNat 64 (p.regs 0) := hp.1 0 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (0#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 0) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.LdrU32.addr x 0#5 0#12 = R14E17.dataVA p (.pin 0 (0)) := by
    unfold MemClass.LdrU32.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (0) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 0 (0), 4) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G0_c05.pin : Int) + G0_c05.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 0 (0)) + BitVec.ofNat 64 t := fun t => by
    simp only [G0_c05]; rw [pinv_of p 0 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 0 (0), 4) (by decide) G0_c05 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 4 → bytePA G0_c05 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU32.addr x 0#5 0#12) = some q → ∀ t : Nat, t < 4 → bytePA G0_c05 (0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have cov : ∀ ds σ, compileRun regions_c05 σ0_c05 inputs.length (plan_c05.take 13) = some (ds, σ) →
      ∀ t : Nat, t < 4 → ∃ i k', σ.memB G0_c05 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c05 σ0_c05 n0_c05 (plan_c05.take 13)).map
        (fun q => (List.range 4).all fun t => (q.2.memB G0_c05 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G0_c05 0 4 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU32.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) 0#12 0#5 x := by
    unfold ArmCertMemPipe.LdrU32.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(13, .pin 0 (0), 4, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 0#5 0#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 0#5 0#12 1#2 2#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrWUoff.dispatch_at real pc 8#5 0#5 0#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU32.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 13 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 0#5 0#12) 630 (by decide) 0#12 0#5 8#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 13 + 4#64 = offset_c05 14 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G0_c05 0 lin [((.x 8), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 13) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_13

#check "CURRENT_DECL step_c05_18"
theorem step_c05_18 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 18 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 18 < capacity)
    (drawBound : past 18 + 1 ≤ past (18 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 8) 18 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x7c, 0xf9400bf3)) (by decide) offset_c05 budget 18 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrXUoffSP.selected 19#5 2#12 = BitVec.ofNat 32 (0x7c, 0xf9400bf3).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c05).getD 77 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c05).getD 77 0 := hreg
  have hptr := ptr_c05_18 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 72 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffe0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : MemClass.LdrU64Sp.addr x 2#12 = R14E17.dataVA p (.pin 31 (-16)) := by
    unfold MemClass.LdrU64Sp.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK2 _ (-16) _ _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-16), 8) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + ((16 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + 8 * (2 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-16), 8) (by decide) G31_c05 (by decide) 16 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 8 → bytePA G31_c05 (16 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU64Sp.addr x 2#12) = some q → ∀ t : Nat, t < 8 → bytePA G31_c05 (8 * 2 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have cov : ∀ ds σ, compileRun regions_c05 σ0_c05 inputs.length (plan_c05.take 18) = some (ds, σ) →
      ∀ t : Nat, t < 8 → ∃ i k', σ.memB G31_c05 (16 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c05 σ0_c05 n0_c05 (plan_c05.take 18)).map
        (fun q => (List.range 8).all fun t => (q.2.memB G31_c05 (16 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G31_c05 16 8 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU64Sp.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) 2#12 x := by
    unfold ArmCertMemPipe.LdrU64Sp.Facts; exact ⟨hsp16, pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(17, .pin 31 (-16), 8, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrXUoffSP.selected 19#5 2#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 19#5 31#5 2#12 1#2 3#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrXUoffSP.dispatch_at real pc 19#5 2#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU64Sp.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 18 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrXUoffSP.selected 19#5 2#12) 630 (by decide) 2#12 19#5 (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 18 + 4#64 = offset_c05 19 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G31_c05 2 lin [((.x 19), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 18) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_18

#check "CURRENT_DECL step_c05_19"
theorem step_c05_19 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 19 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c05)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 19 < capacity)
    (drawBound : past 19 + 1 ≤ past (19 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 16) 19 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 5) (by decide) rfl
    (c := (0x80, 0xa8c27bfd)) (by decide) offset_c05 budget 19 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdpPost.selected 29#5 30#5 4#7 = BitVec.ofNat 32 (0x80, 0xa8c27bfd).2 := by decide
  obtain ⟨σf, hall⟩ := full_c05 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c05).getD 77 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c05).getD 77 0 := hreg
  have hptr := ptr_c05_19 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 72 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffe0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : x.regs.SP_EL0 = R14E17.dataVA p (.pin 31 (-32)) := by
    rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (-32) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-32), 16) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c05.pin : Int) + G31_c05.off + 8 * (0 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c05]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-32), 16) (by decide) G31_c05 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 16 → bytePA G31_c05 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (x.regs.SP_EL0) = some q → ∀ t : Nat, t < 16 → bytePA G31_c05 (8 * 0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have cov : ∀ ds σ, compileRun regions_c05 σ0_c05 inputs.length (plan_c05.take 19) = some (ds, σ) →
      ∀ t : Nat, t < 16 → ∃ i k', σ.memB G31_c05 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c05 σ0_c05 n0_c05 (plan_c05.take 19)).map
        (fun q => (List.range 16).all fun t => (q.2.memB G31_c05 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G31_c05 0 16 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdpPost.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table) x := by
    unfold ArmCertMemPipe.LdpPost.Facts; exact ⟨hsp16, pa, (by rw [haddr]; exact hmap), mmio, hbytes, (fun acc shape => Or.inl ⟨(18, .pin 31 (-32), 16, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdpPost.selected 29#5 30#5 4#7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx 29#5 31#5 30#5 4#7 1#1 2#2) 609 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdpPost.dispatch_at real pc 29#5 30#5 4#7 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdpPost.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c05 budget 19 catalogue room page (by decide) (NativeEntryBodyDispatch.LdpPost.selected 29#5 30#5 4#7) 609 (by decide) 4#7 29#5 30#5 (by decide) (by decide) (by decide) (32) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c05 19 + 4#64 = offset_c05 20 by decide]) (hw ▸ ob) nodup bytePA regions_c05 G31_c05 0 lin [((.x 29), none), ((.x 30), none), (.sp, some ⟨.add, [.reg .sp, .lit 32#64]⟩)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).map Prod.fst = some D_c05 := by
    rw [hlen]
    exact compiles_D_c05
  have ok : (compileRun regions_c05 σ0_c05 inputs.length plan_c05).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 19) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c05_19

end ReleaseProfile.DefaultRuntime
