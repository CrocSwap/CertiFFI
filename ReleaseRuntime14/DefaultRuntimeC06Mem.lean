-- Generated current physical steps from signed c06 mem rows.
import DefaultRuntimeStepEvidence
import DefaultRuntimePhysicalRoutes
import PipeR14Mem.Physical.Steps_c06
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

#check "CURRENT_DECL step_c06_0"
theorem step_c06_0 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 0 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 0 < capacity)
    (drawBound : past 0 + 1 ≤ past (0 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-48))) true 16) 0 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x0, 0xa9bd7bfd)) (by decide) offset_c06 budget 0 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StpPre.selected 29#5 30#5 122#7 = BitVec.ofNat 32 (0x0, 0xa9bd7bfd).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c06).getD 100 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c06).getD 100 0 := hreg
  have hptr := ptr_c06_0 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 100 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.StpPre.ldpAddr x 122#7 = R14E17.dataVA p (.pin 31 (-48)) := by
    unfold MemClass.StpPre.ldpAddr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (-48) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-48), 16) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-48)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + 8 * (0 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-48)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-48), 16) (by decide) G31_c06 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 16 → bytePA G31_c06 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StpPre.ldpAddr x 122#7) = some q → ∀ t : Nat, t < 16 → bytePA G31_c06 (8 * 0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of0 _ ds.sp16
  have facts : ArmCertMemPipe.StpPre.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c06) 122#7 x := by
    unfold ArmCertMemPipe.StpPre.Facts; exact ⟨hsp16, (by rw [haddr]; exact align), pa, (by rw [haddr]; exact hmap), mmio, (fun i hi => outside i hi), (fun i hi => ⟨(.pin 31 (-48), 16), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(0, .pin 31 (-48), 16, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StpPre.selected 29#5 30#5 122#7) (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx 29#5 31#5 30#5 122#7 0#1 2#2) 616 := by
    intro pc t see; exact NativeEntryBodyDispatch.StpPre.dispatch_at real pc 29#5 30#5 122#7 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStpPre.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 0 catalogue room page (by decide) (NativeEntryBodyDispatch.StpPre.selected 29#5 30#5 122#7) 616 (by decide) 122#7 29#5 30#5 (by decide) (by decide) (-48) (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c06) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 0 + 4#64 = offset_c06 1 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G31_c06 0 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 31 (-48), 16)) (by decide) (r := G31_c06) (by decide) (n := 16) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_pair bf) q' hq') [(.sp, some ⟨.add, [.reg .sp, .lit 18446744073709551568#64]⟩)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 0) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_0

#check "CURRENT_DECL step_c06_1"
theorem step_c06_1 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 1 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 1 < capacity)
    (drawBound : past 1 + 1 ≤ past (1 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) true 8) 1 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x4, 0xf9000bf5)) (by decide) offset_c06 budget 1 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StrXUoffSP.selected 21#5 2#12 = BitVec.ofNat 32 (0x4, 0xf9000bf5).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c06).getD 105 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c06).getD 105 0 := hreg
  have hptr := ptr_c06_1 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 100 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffd0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : MemClass.StrU64Sp.addr x 2#12 = R14E17.dataVA p (.pin 31 (-32)) := by
    unfold MemClass.StrU64Sp.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK2 _ (-32) _ _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-32), 8) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + ((16 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + 8 * (2 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-32), 8) (by decide) G31_c06 (by decide) 16 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 8 → bytePA G31_c06 (16 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StrU64Sp.addr x 2#12) = some q → ∀ t : Nat, t < 8 → bytePA G31_c06 (8 * 2 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have facts : ArmCertMemPipe.StrU64Sp.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c06) 2#12 x := by
    unfold ArmCertMemPipe.StrU64Sp.Facts; exact ⟨hsp16, pa, (by rw [haddr]; exact hmap), mmio, (by rw [haddr]; exact align), (fun i hi => outside i hi), (fun i hi => ⟨(.pin 31 (-32), 8), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(1, .pin 31 (-32), 8, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StrXUoffSP.selected 21#5 2#12) (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 21#5 31#5 2#12 0#2 3#2) 648 := by
    intro pc t see; exact NativeEntryBodyDispatch.StrXUoffSP.dispatch_at real pc 21#5 2#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStrU64Sp.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 1 catalogue room page (by decide) (NativeEntryBodyDispatch.StrXUoffSP.selected 21#5 2#12) 648 (by decide) 2#12 21#5 (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c06) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 1 + 4#64 = offset_c06 2 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G31_c06 2 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 31 (-32), 8)) (by decide) (r := G31_c06) (by decide) (n := 8) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_store bf) q' hq') [] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 1) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_1

#check "CURRENT_DECL step_c06_2"
theorem step_c06_2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 2 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 2 < capacity)
    (drawBound : past 2 + 1 ≤ past (2 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) true 16) 2 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x8, 0xa9024ff4)) (by decide) offset_c06 budget 2 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Stp.selected 20#5 19#5 4#7 = BitVec.ofNat 32 (0x8, 0xa9024ff4).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c06).getD 105 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c06).getD 105 0 := hreg
  have hptr := ptr_c06_2 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 100 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffd0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : ArmCertMem.LdpEval.ldpAddr x 4#7 = R14E17.dataVA p (.pin 31 (-16)) := by
    unfold ArmCertMem.LdpEval.ldpAddr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK2 _ (-16) _ _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-16), 16) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + ((32 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + 8 * (4 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-16), 16) (by decide) G31_c06 (by decide) 32 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 16 → bytePA G31_c06 (32 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (ArmCertMem.LdpEval.ldpAddr x 4#7) = some q → ∀ t : Nat, t < 16 → bytePA G31_c06 (8 * 4 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have facts : ArmCertMemPipe.StpOff.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c06) 4#7 x := by
    unfold ArmCertMemPipe.StpOff.Facts; exact ⟨hsp16, (by rw [haddr]; exact align), pa, (by rw [haddr]; exact hmap), mmio, (fun i hi => outside i hi), (fun i hi => ⟨(.pin 31 (-16), 16), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(2, .pin 31 (-16), 16, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.Stp.selected 20#5 19#5 4#7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset 20#5 31#5 19#5 4#7 0#1 2#2) 617 := by
    intro pc t see; exact NativeEntryBodyDispatch.Stp.dispatch_at real pc 20#5 19#5 4#7 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStpOff.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 2 catalogue room page (by decide) (NativeEntryBodyDispatch.Stp.selected 20#5 19#5 4#7) 617 (by decide) 4#7 20#5 19#5 (by decide) (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c06) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 2 + 4#64 = offset_c06 3 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G31_c06 4 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 31 (-16), 16)) (by decide) (r := G31_c06) (by decide) (n := 16) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_pair bf) q' hq') [] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 2) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_2

#check "CURRENT_DECL step_c06_4"
theorem step_c06_4 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 4 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 4 < capacity)
    (drawBound : past 4 + 1 ≤ past (4 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) false 4) 4 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x10, 0xb9400028)) (by decide) offset_c06 budget 4 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrWUoff.selected 8#5 1#5 0#12 = BitVec.ofNat 32 (0x10, 0xb9400028).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 1) = (extend inputs D_c06).getD 70 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (1#5 : BitVec 5).toNat).val] = (extend inputs D_c06).getD 70 0 := hreg
  have hptr := ptr_c06_4 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 70 0 = BitVec.ofNat 64 (p.regs 1) := hp.1 1 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (1#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 1) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.LdrU32.addr x 1#5 0#12 = R14E17.dataVA p (.pin 1 (0)) := by
    unfold MemClass.LdrU32.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (0) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 1 (0), 4) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G1_c06.pin : Int) + G1_c06.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 1 (0)) + BitVec.ofNat 64 t := fun t => by
    simp only [G1_c06]; rw [pinv_of p 1 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 1 (0), 4) (by decide) G1_c06 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 4 → bytePA G1_c06 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU32.addr x 1#5 0#12) = some q → ∀ t : Nat, t < 4 → bytePA G1_c06 (0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have cov : ∀ ds σ, compileRun regions_c06 σ0_c06 inputs.length (plan_c06.take 4) = some (ds, σ) →
      ∀ t : Nat, t < 4 → ∃ i k', σ.memB G1_c06 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c06 σ0_c06 n0_c06 (plan_c06.take 4)).map
        (fun q => (List.range 4).all fun t => (q.2.memB G1_c06 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G1_c06 0 4 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU32.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) 0#12 1#5 x := by
    unfold ArmCertMemPipe.LdrU32.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(4, .pin 1 (0), 4, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 1#5 0#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 1#5 0#12 1#2 2#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrWUoff.dispatch_at real pc 8#5 1#5 0#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU32.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 4 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 1#5 0#12) 630 (by decide) 0#12 1#5 8#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 4 + 4#64 = offset_c06 5 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G1_c06 0 lin [((.x 8), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 4) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_4

#check "CURRENT_DECL step_c06_5"
theorem step_c06_5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 5 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 5 < capacity)
    (drawBound : past 5 + 1 ≤ past (5 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (8))) false 8) 5 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x14, 0xf9400434)) (by decide) offset_c06 budget 5 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrXUoff.selected 20#5 1#5 1#12 = BitVec.ofNat 32 (0x14, 0xf9400434).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 1) = (extend inputs D_c06).getD 70 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (1#5 : BitVec 5).toNat).val] = (extend inputs D_c06).getD 70 0 := hreg
  have hptr := ptr_c06_5 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 70 0 = BitVec.ofNat 64 (p.regs 1) := hp.1 1 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (1#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 1) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.LdrU64.addr x 1#5 1#12 = R14E17.dataVA p (.pin 1 (8)) := by
    unfold MemClass.LdrU64.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (8) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 1 (8), 8) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G1_c06.pin : Int) + G1_c06.off + ((8 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 1 (8)) + BitVec.ofNat 64 t := fun t => by
    simp only [G1_c06]; rw [pinv_of p 1 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G1_c06.pin : Int) + G1_c06.off + 8 * (1 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 1 (8)) + BitVec.ofNat 64 t := fun t => by
    simp only [G1_c06]; rw [pinv_of p 1 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 1 (8), 8) (by decide) G1_c06 (by decide) 8 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 8 → bytePA G1_c06 (8 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU64.addr x 1#5 1#12) = some q → ∀ t : Nat, t < 8 → bytePA G1_c06 (8 * 1 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have cov : ∀ ds σ, compileRun regions_c06 σ0_c06 inputs.length (plan_c06.take 5) = some (ds, σ) →
      ∀ t : Nat, t < 8 → ∃ i k', σ.memB G1_c06 (8 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c06 σ0_c06 n0_c06 (plan_c06.take 5)).map
        (fun q => (List.range 8).all fun t => (q.2.memB G1_c06 (8 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G1_c06 8 8 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU64.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) 1#12 1#5 x := by
    unfold ArmCertMemPipe.LdrU64.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(5, .pin 1 (8), 8, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrXUoff.selected 20#5 1#5 1#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 20#5 1#5 1#12 1#2 3#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrXUoff.dispatch_at real pc 20#5 1#5 1#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU64.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 5 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrXUoff.selected 20#5 1#5 1#12) 630 (by decide) 1#12 1#5 20#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 5 + 4#64 = offset_c06 6 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G1_c06 1 lin [((.x 20), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 5) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_5

#check "CURRENT_DECL step_c06_10"
theorem step_c06_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 10 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 10 < capacity)
    (drawBound : past 10 + 1 ≤ past (10 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 1 (0))) true 4) 10 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x28, 0xb9000028)) (by decide) offset_c06 budget 10 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StrWUoff.selected 8#5 1#5 0#12 = BitVec.ofNat 32 (0x28, 0xb9000028).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 1) = (extend inputs D_c06).getD 70 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (1#5 : BitVec 5).toNat).val] = (extend inputs D_c06).getD 70 0 := hreg
  have hptr := ptr_c06_10 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 70 0 = BitVec.ofNat 64 (p.regs 1) := hp.1 1 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (1#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 1) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.StrU32.addr x 1#5 0#12 = R14E17.dataVA p (.pin 1 (0)) := by
    unfold MemClass.StrU32.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (0) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 1 (0), 4) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G1_c06.pin : Int) + G1_c06.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 1 (0)) + BitVec.ofNat 64 t := fun t => by
    simp only [G1_c06]; rw [pinv_of p 1 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 1 (0), 4) (by decide) G1_c06 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 4 → bytePA G1_c06 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StrU32.addr x 1#5 0#12) = some q → ∀ t : Nat, t < 4 → bytePA G1_c06 (0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have facts : ArmCertMemPipe.StrU32.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c06) 0#12 1#5 x := by
    unfold ArmCertMemPipe.StrU32.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by rw [haddr]; exact align), (fun i hi => outside i hi), (fun i hi => ⟨(.pin 1 (0), 4), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(10, .pin 1 (0), 4, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StrWUoff.selected 8#5 1#5 0#12) (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 1#5 0#12 0#2 2#2) 648 := by
    intro pc t see; exact NativeEntryBodyDispatch.StrWUoff.dispatch_at real pc 8#5 1#5 0#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStrU32.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 10 catalogue room page (by decide) (NativeEntryBodyDispatch.StrWUoff.selected 8#5 1#5 0#12) 648 (by decide) 0#12 1#5 8#5 (by decide) (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c06) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 10 + 4#64 = offset_c06 11 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G1_c06 0 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.pin 1 (0), 4)) (by decide) (r := G1_c06) (by decide) (n := 4) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_store32 bf) q' hq') [] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 10) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_10

#check "CURRENT_DECL step_c06_11"
theorem step_c06_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 11 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 11 < capacity)
    (drawBound : past 11 + 1 ≤ past (11 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 0 (0))) false 4) 11 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x2c, 0xb9400008)) (by decide) offset_c06 budget 11 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrWUoff.selected 8#5 0#5 0#12 = BitVec.ofNat 32 (0x2c, 0xb9400008).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 0) = (extend inputs D_c06).getD 69 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (0#5 : BitVec 5).toNat).val] = (extend inputs D_c06).getD 69 0 := hreg
  have hptr := ptr_c06_11 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 69 0 = BitVec.ofNat 64 (p.regs 0) := hp.1 0 (by decide)
  have hv : x.regs.gpr[(GPRSummary.key (0#5 : BitVec 5).toNat).val] = BitVec.ofNat 64 (p.regs 0) := hx.trans (hptr.trans hpR)
  have haddr : MemClass.LdrU32.addr x 0#5 0#12 = R14E17.dataVA p (.pin 0 (0)) := by
    unfold MemClass.LdrU32.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (0) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 0 (0), 4) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G0_c06.pin : Int) + G0_c06.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 0 (0)) + BitVec.ofNat 64 t := fun t => by
    simp only [G0_c06]; rw [pinv_of p 0 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 0 (0), 4) (by decide) G0_c06 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 4 → bytePA G0_c06 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU32.addr x 0#5 0#12) = some q → ∀ t : Nat, t < 4 → bytePA G0_c06 (0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have cov : ∀ ds σ, compileRun regions_c06 σ0_c06 inputs.length (plan_c06.take 11) = some (ds, σ) →
      ∀ t : Nat, t < 4 → ∃ i k', σ.memB G0_c06 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c06 σ0_c06 n0_c06 (plan_c06.take 11)).map
        (fun q => (List.range 4).all fun t => (q.2.memB G0_c06 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G0_c06 0 4 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU32.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) 0#12 0#5 x := by
    unfold ArmCertMemPipe.LdrU32.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(11, .pin 0 (0), 4, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 0#5 0#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 0#5 0#12 1#2 2#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrWUoff.dispatch_at real pc 8#5 0#5 0#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU32.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 11 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrWUoff.selected 8#5 0#5 0#12) 630 (by decide) 0#12 0#5 8#5 (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 11 + 4#64 = offset_c06 12 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G0_c06 0 lin [((.x 8), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 11) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_11

#check "CURRENT_DECL step_c06_16"
theorem step_c06_16 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 16 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 16 < capacity)
    (drawBound : past 16 + 1 ≤ past (16 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24")) true 1) 16 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x48, 0x39006128)) (by decide) offset_c06 budget 16 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.StrbUoff.selected 8#5 9#5 24#12 = BitVec.ofNat 32 (0x48, 0x39006128).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x (.x 9) = (extend inputs D_c06).getD 121 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.gpr[(GPRSummary.key (9#5 : BitVec 5).toNat).val] = (extend inputs D_c06).getD 121 0 := hreg
  have hptr := ptr_c06_16 inputs (by rw [hlen]; rfl)
  have haddr : MemClass.StrbU.addr x 9#5 24#12 = R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24") := by
    unfold MemClass.StrbU.addr; rw [hx, hptr]; simp only [R14E17.dataVA, R14E17.baseVA]
    rw [hp.2 "x0+mem64[x1+8]+24" (by decide), ofInt_toNat]
    simp only [formVal, op_add, op_lsr]
    rfl
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.indirect "x0+mem64[x1+8]+24", 1) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G32_c06.pin : Int) + G32_c06.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.indirect "x0+mem64[x1+8]+24") + BitVec.ofNat 64 t := fun t => by
    simp only [G32_c06]; rw [pinv_32]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.indirect "x0+mem64[x1+8]+24", 1) (by decide) G32_c06 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 1 → bytePA G32_c06 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.StrbU.addr x 9#5 24#12) = some q → bytePA G32_c06 0 = some q := by
    intro q hq; rw [haddr, hmap] at hq; cases hq; have := lin0 0 (by decide); simpa using this
  have facts : ArmCertMemPipe.StrbU.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) (PipeR14.Physical.DataPA mapping p dataSites_c06) 24#12 9#5 x := by
    unfold ArmCertMemPipe.StrbU.Facts; exact ⟨pa, (by rw [haddr]; exact hmap), mmio, (fun i hi => outside i hi), (fun i hi => ⟨(.indirect "x0+mem64[x1+8]+24", 1), by decide, pa.toNat, hmap, by omega, by omega⟩), (fun acc shape => Or.inl ⟨(16, .indirect "x0+mem64[x1+8]+24", 1, true), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.StrbUoff.selected 8#5 9#5 24#12) (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned 8#5 9#5 24#12 0#2 0#2) 651 := by
    intro pc t see; exact NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc 8#5 9#5 24#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultStrbU.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 16 catalogue room page (by decide) (NativeEntryBodyDispatch.StrbUoff.selected 8#5 9#5 24#12) 651 (by decide) 24#12 9#5 8#5 (by decide) (by decide) dispatch (by decide) (PipeR14.Physical.DataPA mapping p dataSites_c06) ds.code x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 16 + 4#64 = offset_c06 17 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G32_c06 0 lin (fun q hq r' hr' j' hj' bf q' hq' => by rw [haddr, hmap] at hq; cases hq; exact miss_of ds (s := (.indirect "x0+mem64[x1+8]+24", 1)) (by decide) (r := G32_c06) (by decide) (n := 1) (by decide) (by decide) (fun t ht => hvaB t) hmap r' hr' j' hj' (bf_storeb bf) q' hq') [] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 16) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_16

#check "CURRENT_DECL step_c06_17"
theorem step_c06_17 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 17 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 17 < capacity)
    (drawBound : past 17 + 1 ≤ past (17 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-16))) false 16) 17 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x4c, 0xa9424ff4)) (by decide) offset_c06 budget 17 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.Ldp.selected 20#5 19#5 4#7 = BitVec.ofNat 32 (0x4c, 0xa9424ff4).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c06).getD 105 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c06).getD 105 0 := hreg
  have hptr := ptr_c06_17 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 100 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffd0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : ArmCertMem.LdpEval.ldpAddr x 4#7 = R14E17.dataVA p (.pin 31 (-16)) := by
    unfold ArmCertMem.LdpEval.ldpAddr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK2 _ (-16) _ _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-16), 16) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + ((32 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + 8 * (4 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-16)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-16), 16) (by decide) G31_c06 (by decide) 32 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 16 → bytePA G31_c06 (32 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (ArmCertMem.LdpEval.ldpAddr x 4#7) = some q → ∀ t : Nat, t < 16 → bytePA G31_c06 (8 * 4 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have cov : ∀ ds σ, compileRun regions_c06 σ0_c06 inputs.length (plan_c06.take 17) = some (ds, σ) →
      ∀ t : Nat, t < 16 → ∃ i k', σ.memB G31_c06 (32 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c06 σ0_c06 n0_c06 (plan_c06.take 17)).map
        (fun q => (List.range 16).all fun t => (q.2.memB G31_c06 (32 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G31_c06 32 16 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdpOff.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) 4#7 x := by
    unfold ArmCertMemPipe.LdpOff.Facts; exact ⟨hsp16, (by rw [haddr]; exact align), pa, (by rw [haddr]; exact hmap), mmio, hbytes, (fun acc shape => Or.inl ⟨(17, .pin 31 (-16), 16, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.Ldp.selected 20#5 19#5 4#7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset 20#5 31#5 19#5 4#7 1#1 2#2) 611 := by
    intro pc t see; exact NativeEntryBodyDispatch.Ldp.dispatch_at real pc 20#5 19#5 4#7 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdpOff.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 17 catalogue room page (by decide) (NativeEntryBodyDispatch.Ldp.selected 20#5 19#5 4#7) 611 (by decide) 4#7 20#5 19#5 (by decide) (by decide) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 17 + 4#64 = offset_c06 18 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G31_c06 4 lin [((.x 20), none), ((.x 19), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 17) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_17

#check "CURRENT_DECL step_c06_18"
theorem step_c06_18 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 18 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 18 < capacity)
    (drawBound : past 18 + 1 ≤ past (18 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-32))) false 8) 18 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x50, 0xf9400bf5)) (by decide) offset_c06 budget 18 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdrXUoffSP.selected 21#5 2#12 = BitVec.ofNat 32 (0x50, 0xf9400bf5).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c06).getD 105 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c06).getD 105 0 := hreg
  have hptr := ptr_c06_18 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 100 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffd0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : MemClass.LdrU64Sp.addr x 2#12 = R14E17.dataVA p (.pin 31 (-32)) := by
    unfold MemClass.LdrU64Sp.addr; rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK2 _ (-32) _ _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-32), 8) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + ((16 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + 8 * (2 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-32)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-32), 8) (by decide) G31_c06 (by decide) 16 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 8 → bytePA G31_c06 (16 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (MemClass.LdrU64Sp.addr x 2#12) = some q → ∀ t : Nat, t < 8 → bytePA G31_c06 (8 * 2 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have cov : ∀ ds σ, compileRun regions_c06 σ0_c06 inputs.length (plan_c06.take 18) = some (ds, σ) →
      ∀ t : Nat, t < 8 → ∃ i k', σ.memB G31_c06 (16 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c06 σ0_c06 n0_c06 (plan_c06.take 18)).map
        (fun q => (List.range 8).all fun t => (q.2.memB G31_c06 (16 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G31_c06 16 8 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdrU64Sp.Facts spec config rows mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) 2#12 x := by
    unfold ArmCertMemPipe.LdrU64Sp.Facts; exact ⟨hsp16, pa, (by rw [haddr]; exact hmap), mmio, (by simpa using outside 0 (by decide)), (by rw [haddr]; exact align), hbytes, (fun acc shape => Or.inl ⟨(18, .pin 31 (-32), 8, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdrXUoffSP.selected 21#5 2#12) (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned 21#5 31#5 2#12 1#2 3#2) 630 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdrXUoffSP.dispatch_at real pc 21#5 2#12 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdrU64Sp.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 18 catalogue room page (by decide) (NativeEntryBodyDispatch.LdrXUoffSP.selected 21#5 2#12) 630 (by decide) 2#12 21#5 (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 18 + 4#64 = offset_c06 19 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G31_c06 2 lin [((.x 21), none)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 18) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_18

#check "CURRENT_DECL step_c06_19"
theorem step_c06_19 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte) (room : 19 < budget)
    (page : base.toNat % 4096 = 0) (hlen : inputs.length = n0_c06)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base)
    (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat)
    (statusRoom : past 19 < capacity)
    (drawBound : past 19 + 1 ≤ past (19 + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    StepEvidence real spec mapping (ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity past) (HeapV2StepCerts.DataRecs.dataRecs spec (R14E17.dataVA p (.pin 31 (-48))) false 16) 19 := by
  intro x inv
  have ob := fetchR14 spec config rows mapping table sc bytes b cb base ifunc p cs (n := 6) (by decide) rfl
    (c := (0x54, 0xa8c37bfd)) (by decide) offset_c06 budget 19 (by decide) x inv.core
  have hw : NativeEntryBodyDispatch.LdpPost.selected 29#5 30#5 6#7 = BitVec.ofNat 32 (0x54, 0xa8c37bfd).2 := by decide
  obtain ⟨σf, hall⟩ := full_c06 inputs hlen
  have hreg : HeapV2StepCerts.RegBind.regVal x .sp = (extend inputs D_c06).getD 105 0 :=
    ArmCertPipe.Physical.regVal_of_agreesAt inv.extra hall (by rw [hlen]; decide)
  have hx : x.regs.SP_EL0 = (extend inputs D_c06).getD 105 0 := hreg
  have hptr := ptr_c06_19 inputs (by rw [hlen]; rfl)
  have hpR : inputs.getD 100 0 = BitVec.ofNat 64 (p.regs 31) := hp.1 31 (by decide)
  have hv : x.regs.SP_EL0 = BitVec.ofNat 64 (p.regs 31) + 0xffffffffffffffd0#64 := by rw [hx, hptr, op_add, hpR]
  have haddr : x.regs.SP_EL0 = R14E17.dataVA p (.pin 31 (-48)) := by
    rw [hv]; unfold R14E17.dataVA R14E17.baseVA
    exact addrK1 _ (-48) _ (by decide)
  obtain ⟨pa, hmap, mmio, outside, align⟩ := ds.site (.pin 31 (-48), 16) (by decide)
  have hvaB : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + ((0 + t : Nat) : Int)) =
      R14E17.dataVA p (.pin 31 (-48)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have hvaW : ∀ t : Nat, BitVec.ofInt 64 ((pinv p G31_c06.pin : Int) + G31_c06.off + 8 * (0 : Int) + (t : Int)) =
      R14E17.dataVA p (.pin 31 (-48)) + BitVec.ofNat 64 t := fun t => by
    simp only [G31_c06]; rw [pinv_of p 31 (by decide) (by decide)]; simp only [R14E17.dataVA, R14E17.baseVA]; exact va_eq t (by omega)
  have span0 := ds.span (.pin 31 (-48), 16) (by decide) G31_c06 (by decide) 0 (by decide)
    (fun t ht => hvaB t)
  have lin0 : ∀ t : Nat, t < 16 → bytePA G31_c06 (0 + t) = some (pa.toNat + t) :=
    fun t ht => by rw [span0 t ht, ArmCertValue.Physical.spanPA, hmap]; rfl
  have lin : ∀ q : Nat, mapping (x.regs.SP_EL0) = some q → ∀ t : Nat, t < 16 → bytePA G31_c06 (8 * 0 + t) = some (q + t) := by
    intro q hq t ht; rw [haddr, hmap] at hq; cases hq; exact lin0 t ht
  have hsp16 : x.regs.SP_EL0.toNat % 16 = 0 := by
    rw [hv]; exact sp16_of _ _ ds.sp16 (by decide)
  have cov : ∀ ds σ, compileRun regions_c06 σ0_c06 inputs.length (plan_c06.take 19) = some (ds, σ) →
      ∀ t : Nat, t < 16 → ∃ i k', σ.memB G31_c06 (0 + t) = some (i, k') := by
    intro ds' σ h t ht; rw [hlen] at h
    have c0 : (compileRun regions_c06 σ0_c06 n0_c06 (plan_c06.take 19)).map
        (fun q => (List.range 16).all fun t => (q.2.memB G31_c06 (0 + t)).isSome) = some true := by decide
    rw [h] at c0; simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range] at c0
    obtain ⟨⟨i, k'⟩, e⟩ := Option.isSome_iff_exists.1 (c0 t ht); exact ⟨i, k', e⟩
  have hbytes := ArmCertMemPipe.PhysicalFactsG.bytes_of_agreesAt inv.extra G31_c06 0 16 pa.toNat lin0 cov
  have facts : ArmCertMemPipe.LdpPost.Facts spec mapping (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table) x := by
    unfold ArmCertMemPipe.LdpPost.Facts; exact ⟨hsp16, pa, (by rw [haddr]; exact hmap), mmio, hbytes, (fun acc shape => Or.inl ⟨(19, .pin 31 (-48), 16, false), by decide, haddr, rfl, shape⟩)⟩
  have dispatch : ArmBridge.CruxGenGuarded.DispatchAt real (NativeEntryBodyDispatch.LdpPost.selected 29#5 30#5 6#7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx 29#5 31#5 30#5 6#7 1#1 2#2) 609 := by
    intro pc t see; exact NativeEntryBodyDispatch.LdpPost.dispatch_at real pc 29#5 30#5 6#7 t (by simpa using see)
  obtain ⟨fin, run, core, vh, z, dit, ev, mv, choice⟩ := ReleaseProfile.DefaultLdpPost.routePhysical real spec config rows mapping _ sc (referenceImageI bytes base ifunc) base cs.separated base offset_c06 budget 19 catalogue room page (by decide) (NativeEntryBodyDispatch.LdpPost.selected 29#5 30#5 6#7) 609 (by decide) 6#7 29#5 30#5 (by decide) (by decide) (by decide) (48) (by decide) dispatch (by decide) x inv.core (current_status inv statusRoom) facts (by rw [inv.core.v1.pc, BitVec.add_assoc, show offset_c06 19 + 4#64 = offset_c06 20 by decide]) (hw ▸ ob) nodup bytePA regions_c06 G31_c06 0 lin [((.x 29), none), ((.x 30), none), (.sp, some ⟨.add, [.reg .sp, .lit 48#64]⟩)] (by decide)
  rw [haddr] at ev

  have hc : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).map Prod.fst = some D_c06 := by
    rw [hlen]
    exact compiles_D_c06
  have ok : (compileRun regions_c06 σ0_c06 inputs.length plan_c06).isSome = true := by
    have h := congrArg Option.isSome hc
    rw [Option.isSome_map] at h
    exact h
  have next := ArmCertPipe.Physical.agreesAt_succ (k := 19) (by decide) ok inv.extra vh mv
  exact ⟨fin, run, inv.advance core next choice drawBound, z, dit, ev⟩

#print axioms step_c06_19

end ReleaseProfile.DefaultRuntime
