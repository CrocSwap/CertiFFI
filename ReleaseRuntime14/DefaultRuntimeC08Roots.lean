-- Generated semantic, frame, and trace projections from the current runtime run.
import DefaultRuntimeC08Run
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

#check "CURRENT_DECL release_fullpc_c08"
theorem release_fullpc_c08
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
    (hlen : inputs.length = n0_c08)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget bytePA regions_c08 σ0_c08 inputs plan_c08 catalogue capacity_c08 past_c08 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c08 0 inputs ∧
      (∀ q ∈ outMemLocs_c08.zip outMem_c08, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c08 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 18 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 19 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 20 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 21 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 22 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 23 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 24 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 25 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 26 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 27 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 28 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 29 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 30 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 31 0 ∧
      fin.regs._Z = entry.regs._Z ∧
      fin.regs.PSTATE.N.setWidth 64 = inputs.getD 32 0 ∧
      fin.regs.PSTATE.Z.setWidth 64 = inputs.getD 33 0 ∧
      fin.regs.PSTATE.C.setWidth 64 = inputs.getD 34 0 ∧
      fin.regs.PSTATE.V.setWidth 64 = inputs.getD 35 0) ∧
      fin.regs._PC = base + BitVec.ofNat 64 0x2baa78 := by
  obtain ⟨_, fin, run, hA, pc, hz, _⟩ :=
    run_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs dp.page dp.low hlen hpath catalogue dp.nodup dp.room entry dp.init
  obtain ⟨σf, hall⟩ : ∃ σf, compileRun regions_c08 σ0_c08 inputs.length plan_c08 = some (D_c08, σf) := by
    have hD := compiles_D_c08
    rw [← hlen] at hD
    cases hq : compileRun regions_c08 σ0_c08 inputs.length plan_c08 with
    | none => rw [hq] at hD; cases hD
    | some q =>
      rw [hq] at hD
      simp only [Option.map_some] at hD
      have h1 : q.1 = D_c08 := Option.some.inj hD
      exact ⟨q.2, by rw [← h1]⟩
  have hE := ArmCertPipe.Physical.agrees_end hA hall
  have hR := frameRegs_c08
  rw [← hlen, hall] at hR
  simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at hR
  obtain ⟨h0, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hsp⟩ := hR
  have v18 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 18 0 := by
    rw [hE.1 _ _ h18]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v19 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 19 0 := by
    rw [hE.1 _ _ h19]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v20 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 20 0 := by
    rw [hE.1 _ _ h20]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v21 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 21 0 := by
    rw [hE.1 _ _ h21]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v22 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 22 0 := by
    rw [hE.1 _ _ h22]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v23 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 23 0 := by
    rw [hE.1 _ _ h23]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v24 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 24 0 := by
    rw [hE.1 _ _ h24]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v25 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 25 0 := by
    rw [hE.1 _ _ h25]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v26 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 26 0 := by
    rw [hE.1 _ _ h26]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v27 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 27 0 := by
    rw [hE.1 _ _ h27]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v28 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 28 0 := by
    rw [hE.1 _ _ h28]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v29 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 29 0 := by
    rw [hE.1 _ _ h29]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v30 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 30 0 := by
    rw [hE.1 _ _ h30]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have vsp : HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 31 0 := by
    rw [hE.1 _ _ hsp]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have hn := frameNZCV_c08
  rw [← hlen, hall] at hn
  simp only [Option.map_some] at hn
  obtain ⟨vN, vZ, vC, vV⟩ := hE.2.1 _ _ _ _ (Option.some.inj hn)
  rw [NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)] at vN vZ vC vV
  have S := PipeR14M.spec_c08 inputs (by rw [hlen]; rfl)
  have key : ∀ q ∈ outMemLocs_c08.zip outMem_c08,
      (match q.2 with | some (i, _) => decide (i ∈ PipeR14M.outIds_c08) | none => true) = true := by decide
  have outMap : outMemLocs_c08.map (fun (g, j) => σf.memB g j) = outMem_c08 := by
    have h := outMem_ok_c08
    rw [← hlen, hall] at h
    exact Option.some.inj h
  have outputs := ArmCertPipe.Physical.outMem_end hE _ _ outMap
  have finalPC : fin.regs._PC = base + BitVec.ofNat 64 0x2baa78 := by exact pc
  refine ⟨fin, run, ⟨?_, ?_, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, vsp, hz, vN, vZ, vC, vV⟩, finalPC⟩
  · exact (hE.1 _ _ h0).trans (S 0 (by decide))
  · intro q hq i b hb
    have valid := key q hq
    rw [hb] at valid
    have h := S i (by simpa using valid)
    rw [outputs q hq i b hb]
    simp only [evalDefs] at h
    rw [h]

#print axioms release_fullpc_c08

#check "CURRENT_DECL release_full_c08"
theorem release_full_c08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c08) (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget bytePA regions_c08 σ0_c08 inputs plan_c08 catalogue capacity_c08 past_c08 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c08 0 inputs ∧
      (∀ q ∈ outMemLocs_c08.zip outMem_c08, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c08 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 18 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 19 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 20 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 21 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 22 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 23 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 24 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 25 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 26 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 27 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 28 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 29 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 30 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 31 0 ∧
      fin.regs._Z = entry.regs._Z ∧
      fin.regs.PSTATE.N.setWidth 64 = inputs.getD 32 0 ∧
      fin.regs.PSTATE.Z.setWidth 64 = inputs.getD 33 0 ∧
      fin.regs.PSTATE.C.setWidth 64 = inputs.getD 34 0 ∧
      fin.regs.PSTATE.V.setWidth 64 = inputs.getD 35 0 := by
  obtain ⟨fin, hs, hF, _⟩ := release_fullpc_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs hlen hpath catalogue entry dp
  exact ⟨fin, hs, hF⟩

#print axioms release_full_c08

#check "CURRENT_DECL release_ct_c08"
theorem release_ct_c08
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c08)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c08) guards_c08)
    (entry1 : NativeState)
    (dp1 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget bytePA regions_c08 σ0_c08 inputs1 plan_c08 catalogue1 capacity_c08 past_c08 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c08)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c08) guards_c08)
    (entry2 : NativeState)
    (dp2 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget bytePA regions_c08 σ0_c08 inputs2 plan_c08 catalogue2 capacity_c08 past_c08 entry2) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c08.length) (stateAt real entry2 plan_c08.length) := by
  obtain ⟨inv1, fin1, run1, _, pc1, _, ev1⟩ :=
    run_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
      dp1.page dp1.low hlen1 hpath1 catalogue1 nodup dp1.room entry1 dp1.init
  obtain ⟨inv2, fin2, run2, _, pc2, _, ev2⟩ :=
    run_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
      dp2.page dp2.low hlen2 hpath2 catalogue2 nodup dp2.room entry2 dp2.init
  have len : plan_c08.length = 1 := rfl
  have hL : 0 < plan_c08.length := by omega
  refine PhasedCT.phased_records (stateAt real entry1) (stateAt real entry2)
    (fun _ _ _ => True) plan_c08.length trivial
    (by rw [(inv1 0 hL).core.v1.pc, (inv2 0 hL).core.v1.pc]) ?_
  intro k hk _
  have pc : (stateAt real entry1 k).regs._PC = (stateAt real entry2 k).regs._PC := by
    rw [(inv1 k hk).core.v1.pc, (inv2 k hk).core.v1.pc]
  refine ⟨?_, trivial⟩
  by_cases earlier : k + 1 < plan_c08.length
  · obtain ⟨f1, r1, n1, _, _, e1⟩ :=
      steps_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
        dp1.page dp1.low hlen1 hpath1 catalogue1 entry1 nodup dp1.room k earlier _ (inv1 k hk)
    obtain ⟨f2, r2, n2, _, _, e2⟩ :=
      steps_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
        dp2.page dp2.low hlen2 hpath2 catalogue2 entry2 nodup dp2.room k earlier _ (inv2 k hk)
    rw [ArmCertValue.Physical.stateAt_succ_of' r1, ArmCertValue.Physical.stateAt_succ_of' r2]
    exact StepEvents.pair spec mapping (records_c08 spec p k) _ _ _ _ e1 e2 pc
      (by rw [n1.core.v1.pc, n2.core.v1.pc])
  · have last : k = plan_c08.length - 1 := by omega
    subst k
    rw [ArmCertValue.Physical.stateAt_succ_of' run1, ArmCertValue.Physical.stateAt_succ_of' run2]
    exact StepEvents.pair spec mapping (records_c08 spec p 0) _ _ _ _ ev1 ev2 pc (pc1.trans pc2.symm)


#print axioms release_ct_c08
end ReleaseProfile.DefaultRuntime
