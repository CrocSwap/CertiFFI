-- Generated semantic, frame, and trace projections from the current runtime run.
import DefaultRuntimeC02Run
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

#check "CURRENT_DECL release_fullpc_c02"
theorem release_fullpc_c02
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
    (hlen : inputs.length = n0_c02)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c02) guards_c02)
    (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c02 regions_c02 sc base)
    (hp : PinsAgree p rs_c02 forms_c02 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c02 R14Plan.codeWords_c02 R14Plan.entry_c02 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c02 budget bytePA regions_c02 σ0_c02 inputs plan_c02 catalogue capacity_c02 past_c02 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c02.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c02 106 inputs ∧
      (∀ q ∈ outMemLocs_c02.zip outMem_c02, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c02 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 71 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 72 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 73 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 74 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 75 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 76 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 77 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 78 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 79 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 80 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 81 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 82 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 83 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 84 0 ∧
      fin.regs._Z = entry.regs._Z) ∧
      fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) := by
  obtain ⟨_, fin, run, hA, pc, hz, _⟩ :=
    run_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs dp.page dp.low hlen hpath hlr ds hp catalogue dp.nodup dp.room entry dp.init
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c02 σ0_c02 inputs.length plan_c02 = some (D_c02, σf) := by
    have hD := compiles_D_c02
    rw [← hlen] at hD
    cases hq : compileRun regions_c02 σ0_c02 inputs.length plan_c02 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c02 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hE := ArmCertPipe.Physical.agrees_end hA hall
  have hR := frameRegs_c02
  rw [← hlen, hall] at hR
  simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at hR
  obtain ⟨h0, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hsp⟩ := hR
  have v18 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 71 0 := by
    rw [hE.1 _ _ h18]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v19 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 72 0 := by
    rw [hE.1 _ _ h19]
    have h := NativeR14Ret.extend_getD_def inputs D_c02 19 (by decide)
    rw [show inputs.length + 19 = 108 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c02[19]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 72)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c02.take 19)).getD 72 0 = inputs.getD 72 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v20 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 73 0 := by
    rw [hE.1 _ _ h20]
    have h := NativeR14Ret.extend_getD_def inputs D_c02 18 (by decide)
    rw [show inputs.length + 18 = 107 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c02[18]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 73)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c02.take 18)).getD 73 0 = inputs.getD 73 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v21 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 74 0 := by
    rw [hE.1 _ _ h21]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v22 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 75 0 := by
    rw [hE.1 _ _ h22]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v23 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 76 0 := by
    rw [hE.1 _ _ h23]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v24 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 77 0 := by
    rw [hE.1 _ _ h24]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v25 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 78 0 := by
    rw [hE.1 _ _ h25]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v26 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 79 0 := by
    rw [hE.1 _ _ h26]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v27 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 80 0 := by
    rw [hE.1 _ _ h27]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v28 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 81 0 := by
    rw [hE.1 _ _ h28]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v29 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 82 0 := by
    rw [hE.1 _ _ h29]
    have h := NativeR14Ret.extend_getD_def inputs D_c02 21 (by decide)
    rw [show inputs.length + 21 = 110 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c02[21]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 82)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c02.take 21)).getD 82 0 = inputs.getD 82 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v30 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 83 0 := by
    rw [hE.1 _ _ h30]
    have h := NativeR14Ret.extend_getD_def inputs D_c02 22 (by decide)
    rw [show inputs.length + 22 = 111 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c02[22]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 83)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c02.take 22)).getD 83 0 = inputs.getD 83 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have vsp : HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 84 0 := by
    rw [hE.1 _ _ hsp]
    have h := NativeR14Ret.extend_getD_def inputs D_c02 20 (by decide)
    rw [show inputs.length + 20 = 109 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c02[20]'(by decide) = ⟨.add, [.id 89, .imm 0x0000000000000020#64]⟩ := by decide
    rw [hd]
    simp only [Def.eval, List.map, Arg.eval]
    have h2 := NativeR14Ret.extend_getD_def inputs (D_c02.take 20) 0 (by decide)
    rw [show inputs.length + 0 = 89 by rw [hlen]; decide] at h2
    rw [h2]
    have hd2 : (D_c02.take 20)[0]'(by decide) = ⟨.add, [.id 84, .imm 0xffffffffffffffe0#64]⟩ := by decide
    rw [hd2]
    simp only [Def.eval, List.map, Arg.eval]
    rw [NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide), op_add, op_add, BitVec.add_assoc,
      show (0xffffffffffffffe0#64 : BitVec 64) + 0x0000000000000020#64 = 0#64 by decide, BitVec.add_zero]
  have S := PipeR14M.spec_c02 inputs (by rw [hlen]; rfl)
  have key : ∀ q ∈ outMemLocs_c02.zip outMem_c02,
      (match q.2 with | some (i, _) => decide (i ∈ PipeR14M.outIds_c02) | none => true) = true := by decide
  have outMap : outMemLocs_c02.map (fun (g, j) => σf.memB g j) = outMem_c02 := by
    have h := outMem_ok_c02
    rw [← hlen, hall] at h
    exact Option.some.inj h
  have outputs := ArmCertPipe.Physical.outMem_end hE _ _ outMap
  have entryLR := ArmCertPipe.Physical.regVal_of_agreesAt
    (r := .x ⟨30, by decide⟩) (i := 83) dp.init.extra hall (by rw [hlen]; decide)
  have finalPC : fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) := by
    rw [pc, entryLR]
    exact (NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)).symm
  refine ⟨fin, run, ⟨?_, ?_, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, vsp, hz⟩, finalPC⟩
  · exact (hE.1 _ _ h0).trans (S 106 (by decide))
  · intro q hq i b hb
    have valid := key q hq
    rw [hb] at valid
    have h := S i (by simpa using valid)
    rw [outputs q hq i b hb]
    simp only [evalDefs] at h
    rw [h]

#print axioms release_fullpc_c02

#check "CURRENT_DECL release_full_c02"
theorem release_full_c02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c02) (hpath : ArmCertPipe.PathOK (extend inputs D_c02) guards_c02) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c02 regions_c02 sc base) (hp : PinsAgree p rs_c02 forms_c02 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c02 R14Plan.codeWords_c02 R14Plan.entry_c02 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c02 budget bytePA regions_c02 σ0_c02 inputs plan_c02 catalogue capacity_c02 past_c02 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c02.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c02 106 inputs ∧
      (∀ q ∈ outMemLocs_c02.zip outMem_c02, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c02 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 71 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 72 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 73 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 74 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 75 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 76 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 77 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 78 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 79 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 80 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 81 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 82 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 83 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 84 0 ∧
      fin.regs._Z = entry.regs._Z := by
  obtain ⟨fin, hs, hF, _⟩ := release_fullpc_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs hlen hpath hlr ds hp catalogue entry dp
  exact ⟨fin, hs, hF⟩

#print axioms release_full_c02

#check "CURRENT_DECL release_ct_c02"
theorem release_ct_c02
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
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c02 regions_c02 sc base)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c02)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c02) guards_c02)
    (hlr1 : (inputs1.getD 83 0).toNat < 2 ^ 54)
    (hp1 : PinsAgree p rs_c02 forms_c02 inputs1)
    (entry1 : NativeState)
    (dp1 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c02 R14Plan.codeWords_c02 R14Plan.entry_c02 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c02 budget bytePA regions_c02 σ0_c02 inputs1 plan_c02 catalogue1 capacity_c02 past_c02 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c02)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c02) guards_c02)
    (hlr2 : (inputs2.getD 83 0).toNat < 2 ^ 54)
    (hp2 : PinsAgree p rs_c02 forms_c02 inputs2)
    (entry2 : NativeState)
    (dp2 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c02 R14Plan.codeWords_c02 R14Plan.entry_c02 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c02 budget bytePA regions_c02 σ0_c02 inputs2 plan_c02 catalogue2 capacity_c02 past_c02 entry2)
    (hlr12 : inputs1.getD 83 0 = inputs2.getD 83 0) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c02.length) (stateAt real entry2 plan_c02.length) := by
  obtain ⟨inv1, fin1, run1, _, pc1, _, ev1⟩ :=
    run_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
      dp1.page dp1.low hlen1 hpath1 hlr1 ds hp1 catalogue1 nodup dp1.room entry1 dp1.init
  obtain ⟨inv2, fin2, run2, _, pc2, _, ev2⟩ :=
    run_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
      dp2.page dp2.low hlen2 hpath2 hlr2 ds hp2 catalogue2 nodup dp2.room entry2 dp2.init
  have len : plan_c02.length = 20 := rfl
  have hL : 0 < plan_c02.length := by omega
  refine PhasedCT.phased_records (stateAt real entry1) (stateAt real entry2)
    (fun _ _ _ => True) plan_c02.length trivial
    (by rw [(inv1 0 hL).core.v1.pc, (inv2 0 hL).core.v1.pc]) ?_
  intro k hk _
  have pc : (stateAt real entry1 k).regs._PC = (stateAt real entry2 k).regs._PC := by
    rw [(inv1 k hk).core.v1.pc, (inv2 k hk).core.v1.pc]
  refine ⟨?_, trivial⟩
  by_cases earlier : k + 1 < plan_c02.length
  · obtain ⟨f1, r1, n1, _, _, e1⟩ :=
      steps_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
        dp1.page dp1.low hlen1 hpath1 hlr1 ds hp1 catalogue1 entry1 nodup dp1.room k earlier _ (inv1 k hk)
    obtain ⟨f2, r2, n2, _, _, e2⟩ :=
      steps_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
        dp2.page dp2.low hlen2 hpath2 hlr2 ds hp2 catalogue2 entry2 nodup dp2.room k earlier _ (inv2 k hk)
    rw [ArmCertValue.Physical.stateAt_succ_of' r1, ArmCertValue.Physical.stateAt_succ_of' r2]
    exact StepEvents.pair spec mapping (records_c02 spec p k) _ _ _ _ e1 e2 pc
      (by rw [n1.core.v1.pc, n2.core.v1.pc])
  · have last : k = plan_c02.length - 1 := by omega
    subst k
    rw [ArmCertValue.Physical.stateAt_succ_of' run1, ArmCertValue.Physical.stateAt_succ_of' run2]
    exact StepEvents.pair spec mapping (records_c02 spec p 19) _ _ _ _ ev1 ev2 pc (pc1.trans (hlr12.trans pc2.symm))


#print axioms release_ct_c02
end ReleaseProfile.DefaultRuntime
