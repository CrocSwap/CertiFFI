-- Generated semantic, frame, and trace projections from the current runtime run.
import DefaultRuntimeC05Run
import DefaultRuntimeC00Roots

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime
open PipeR14 PipeR14.Physical

#check "CURRENT_DECL release_fullpc_c05"
theorem release_fullpc_c05
    (real : Type)
    [Sail.SailReal real]
    {domain : QueryDomain}
    (spec : TopologyImageSpec domain)
    (config : AttributeConfig)
    (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (b : Binds bytes R14Scoped.slices)
    (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c05)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c05) guards_c05)
    (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c05 budget bytePA regions_c05 σ0_c05 inputs plan_c05 catalogue capacity_c05 past_c05 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c05.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c05 94 inputs ∧
      (∀ q ∈ outMemLocs_c05.zip outMem_c05, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c05 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 59 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 60 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 61 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 62 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 63 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 64 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 65 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 66 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 67 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 68 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 69 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 70 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 71 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 72 0 ∧
      fin.regs._Z = entry.regs._Z) ∧
      fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) := by
  obtain ⟨_, fin, run, hA, pc, hz, _⟩ :=
    run_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs dp.page dp.low hlen hpath hlr ds hp catalogue dp.nodup dp.room entry dp.init
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c05 σ0_c05 inputs.length plan_c05 = some (D_c05, σf) := by
    have hD := compiles_D_c05
    rw [← hlen] at hD
    cases hq : compileRun regions_c05 σ0_c05 inputs.length plan_c05 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c05 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hE := ArmCertPipe.Physical.agrees_end hA hall
  have hR := frameRegs_c05
  rw [← hlen, hall] at hR
  simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at hR
  obtain ⟨h0, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hsp⟩ := hR
  have v18 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 59 0 := by
    rw [hE.1 _ _ h18]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v19 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 60 0 := by
    rw [hE.1 _ _ h19]
    have h := NativeR14Ret.extend_getD_def inputs D_c05 18 (by decide)
    rw [show inputs.length + 18 = 95 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c05[18]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 60)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c05.take 18)).getD 60 0 = inputs.getD 60 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v20 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 61 0 := by
    rw [hE.1 _ _ h20]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v21 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 62 0 := by
    rw [hE.1 _ _ h21]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v22 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 63 0 := by
    rw [hE.1 _ _ h22]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v23 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 64 0 := by
    rw [hE.1 _ _ h23]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v24 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 65 0 := by
    rw [hE.1 _ _ h24]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v25 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 66 0 := by
    rw [hE.1 _ _ h25]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v26 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 67 0 := by
    rw [hE.1 _ _ h26]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v27 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 68 0 := by
    rw [hE.1 _ _ h27]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v28 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 69 0 := by
    rw [hE.1 _ _ h28]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v29 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 70 0 := by
    rw [hE.1 _ _ h29]
    have h := NativeR14Ret.extend_getD_def inputs D_c05 20 (by decide)
    rw [show inputs.length + 20 = 97 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c05[20]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 70)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c05.take 20)).getD 70 0 = inputs.getD 70 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v30 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 71 0 := by
    rw [hE.1 _ _ h30]
    have h := NativeR14Ret.extend_getD_def inputs D_c05 21 (by decide)
    rw [show inputs.length + 21 = 98 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c05[21]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 71)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c05.take 21)).getD 71 0 = inputs.getD 71 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have vsp : HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 72 0 := by
    rw [hE.1 _ _ hsp]
    have h := NativeR14Ret.extend_getD_def inputs D_c05 19 (by decide)
    rw [show inputs.length + 19 = 96 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c05[19]'(by decide) = ⟨.add, [.id 77, .imm 0x0000000000000020#64]⟩ := by decide
    rw [hd]
    simp only [Def.eval, List.map, Arg.eval]
    have h2 := NativeR14Ret.extend_getD_def inputs (D_c05.take 19) 0 (by decide)
    rw [show inputs.length + 0 = 77 by rw [hlen]; decide] at h2
    rw [h2]
    have hd2 : (D_c05.take 19)[0]'(by decide) = ⟨.add, [.id 72, .imm 0xffffffffffffffe0#64]⟩ := by decide
    rw [hd2]
    simp only [Def.eval, List.map, Arg.eval]
    rw [NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide), op_add, op_add, BitVec.add_assoc,
      show (0xffffffffffffffe0#64 : BitVec 64) + 0x0000000000000020#64 = 0#64 by decide, BitVec.add_zero]
  have S := PipeR14M.spec_c05 inputs (by rw [hlen]; rfl)
  have key : ∀ q ∈ outMemLocs_c05.zip outMem_c05,
      (match q.2 with | some (i, _) => decide (i ∈ PipeR14M.outIds_c05) | none => true) = true := by decide
  have outMap : outMemLocs_c05.map (fun (g, j) => σf.memB g j) = outMem_c05 := by
    have h := outMem_ok_c05
    rw [← hlen, hall] at h
    exact Option.some.inj h
  have outputs := ArmCertPipe.Physical.outMem_end hE _ _ outMap
  have entryLR := ArmCertPipe.Physical.regVal_of_agreesAt
    (r := .x ⟨30, by decide⟩) (i := 71) dp.init.extra hall (by rw [hlen]; decide)
  have finalPC : fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) := by
    rw [pc, entryLR]
    exact (NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)).symm
  refine ⟨fin, run, ⟨?_, ?_, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, vsp, hz⟩, finalPC⟩
  · exact (hE.1 _ _ h0).trans (S 94 (by decide))
  · intro q hq i b hb
    have valid := key q hq
    rw [hb] at valid
    have h := S i (by simpa using valid)
    rw [outputs q hq i b hb]
    simp only [evalDefs] at h
    rw [h]

#print axioms release_fullpc_c05

#check "CURRENT_DECL release_full_c05"
theorem release_full_c05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c05) (hpath : ArmCertPipe.PathOK (extend inputs D_c05) guards_c05) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base) (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c05 budget bytePA regions_c05 σ0_c05 inputs plan_c05 catalogue capacity_c05 past_c05 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c05.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c05 94 inputs ∧
      (∀ q ∈ outMemLocs_c05.zip outMem_c05, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c05 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 59 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 60 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 61 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 62 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 63 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 64 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 65 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 66 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 67 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 68 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 69 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 70 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 71 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 72 0 ∧
      fin.regs._Z = entry.regs._Z := by
  obtain ⟨fin, hs, hF, _⟩ := release_fullpc_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs hlen hpath hlr ds hp catalogue entry dp
  exact ⟨fin, hs, hF⟩

#print axioms release_full_c05

#check "CURRENT_DECL release_ct_c05"
theorem release_ct_c05
    (real : Type)
    [Sail.SailReal real]
    {domain : QueryDomain}
    (spec : TopologyImageSpec domain)
    (config : AttributeConfig)
    (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (b : Binds bytes R14Scoped.slices)
    (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c05)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c05) guards_c05)
    (hlr1 : (inputs1.getD 71 0).toNat < 2 ^ 54)
    (hp1 : PinsAgree p rs_c05 forms_c05 inputs1)
    (entry1 : NativeState)
    (dp1 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c05 budget bytePA regions_c05 σ0_c05 inputs1 plan_c05 catalogue1 capacity_c05 past_c05 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c05)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c05) guards_c05)
    (hlr2 : (inputs2.getD 71 0).toNat < 2 ^ 54)
    (hp2 : PinsAgree p rs_c05 forms_c05 inputs2)
    (entry2 : NativeState)
    (dp2 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c05 budget bytePA regions_c05 σ0_c05 inputs2 plan_c05 catalogue2 capacity_c05 past_c05 entry2)
    (hlr12 : inputs1.getD 71 0 = inputs2.getD 71 0) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c05.length) (stateAt real entry2 plan_c05.length) := by
  obtain ⟨inv1, fin1, run1, _, pc1, _, ev1⟩ :=
    run_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
      dp1.page dp1.low hlen1 hpath1 hlr1 ds hp1 catalogue1 nodup dp1.room entry1 dp1.init
  obtain ⟨inv2, fin2, run2, _, pc2, _, ev2⟩ :=
    run_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
      dp2.page dp2.low hlen2 hpath2 hlr2 ds hp2 catalogue2 nodup dp2.room entry2 dp2.init
  have len : plan_c05.length = 21 := rfl
  have hL : 0 < plan_c05.length := by omega
  refine PhasedCT.phased_records (stateAt real entry1) (stateAt real entry2)
    (fun _ _ _ => True) plan_c05.length trivial
    (by rw [(inv1 0 hL).core.v1.pc, (inv2 0 hL).core.v1.pc]) ?_
  intro k hk _
  have pc : (stateAt real entry1 k).regs._PC = (stateAt real entry2 k).regs._PC := by
    rw [(inv1 k hk).core.v1.pc, (inv2 k hk).core.v1.pc]
  refine ⟨?_, trivial⟩
  by_cases earlier : k + 1 < plan_c05.length
  · obtain ⟨f1, r1, n1, _, _, e1⟩ :=
      steps_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
        dp1.page dp1.low hlen1 hpath1 hlr1 ds hp1 catalogue1 entry1 nodup dp1.room k earlier _ (inv1 k hk)
    obtain ⟨f2, r2, n2, _, _, e2⟩ :=
      steps_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
        dp2.page dp2.low hlen2 hpath2 hlr2 ds hp2 catalogue2 entry2 nodup dp2.room k earlier _ (inv2 k hk)
    rw [ArmCertValue.Physical.stateAt_succ_of' r1, ArmCertValue.Physical.stateAt_succ_of' r2]
    exact StepEvents.pair spec mapping (records_c05 spec p k) _ _ _ _ e1 e2 pc
      (by rw [n1.core.v1.pc, n2.core.v1.pc])
  · have last : k = plan_c05.length - 1 := by omega
    subst k
    rw [ArmCertValue.Physical.stateAt_succ_of' run1, ArmCertValue.Physical.stateAt_succ_of' run2]
    exact StepEvents.pair spec mapping (records_c05 spec p 20) _ _ _ _ ev1 ev2 pc (pc1.trans (hlr12.trans pc2.symm))


#print axioms release_ct_c05
end ReleaseProfile.DefaultRuntime
