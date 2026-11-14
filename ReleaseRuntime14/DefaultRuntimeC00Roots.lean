-- Runtime14 case c00 semantic and frame projections, pending typed admission.
import DefaultRuntimeC00Run
import ReleaseR14.Release.Spec
import ReleaseR14.Pipe.Frame
import PipeR14.PinLink
import NativeR14Ret.Extend

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

structure DeploymentPremises {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (bytePA : ArmCertValue.Physical.BytePA) (regions : List Region)
    (σ0 : Sym) (inputs : List (BitVec 64)) (plan : List StepV) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (past : Nat → Nat) (entry : NativeState) : Prop where
  separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping m
  room : plan.length ≤ budget
  nodup : (spec.logicalRows.map (·.logical)).Nodup
  init : InvPhysical spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan catalogue entry capacity past 0 entry

#check "CURRENT_DECL release_fullpc_c00"
theorem release_fullpc_c00
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
    (hlen : inputs.length = n0_c00)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c00) guards_c00)
    (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base)
    (hp : PinsAgree p rs_c00 forms_c00 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c00 R14Plan.codeWords_c00 R14Plan.entry_c00 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c00 budget bytePA regions_c00 σ0_c00 inputs plan_c00 catalogue capacity_c00 past_c00 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c00.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c00 107 inputs ∧
      (∀ q ∈ outMemLocs_c00.zip outMem_c00, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c00 i inputs) >>> (8 * b)).setWidth 8)) ∧
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
  obtain ⟨_, fin, run, hA, pc, hz, _⟩ := run_c00 real spec config rows mapping table sc bytes b cb base ifunc p
    budget inputs bytePA cs dp.page dp.low hlen hpath hlr ds hp catalogue dp.nodup dp.room entry dp.init
  obtain ⟨σf, hall⟩ := PipeR14.Physical.full_c00 inputs hlen
  have hE := ArmCertPipe.Physical.agrees_end hA hall
  have hR := frameRegs_c00
  rw [← hlen, hall] at hR
  simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at hR
  obtain ⟨h0, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hsp⟩ := hR
  have v18 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 71 0 := by
    rw [hE.1 _ _ h18]; exact NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
  have v19 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 72 0 := by
    rw [hE.1 _ _ h19]
    have h := NativeR14Ret.extend_getD_def inputs D_c00 20 (by decide)
    rw [show inputs.length + 20 = 109 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c00[20]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 72)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c00.take 20)).getD 72 0 = inputs.getD 72 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v20 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 73 0 := by
    rw [hE.1 _ _ h20]
    have h := NativeR14Ret.extend_getD_def inputs D_c00 19 (by decide)
    rw [show inputs.length + 19 = 108 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c00[19]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 73)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c00.take 19)).getD 73 0 = inputs.getD 73 0 :=
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
    have h := NativeR14Ret.extend_getD_def inputs D_c00 22 (by decide)
    rw [show inputs.length + 22 = 111 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c00[22]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 82)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c00.take 22)).getD 82 0 = inputs.getD 82 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have v30 : HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 83 0 := by
    rw [hE.1 _ _ h30]
    have h := NativeR14Ret.extend_getD_def inputs D_c00 23 (by decide)
    rw [show inputs.length + 23 = 112 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c00[23]'(by decide) = ⟨.asm8 [0, 1, 2, 3, 4, 5, 6, 7], List.replicate 8 (.id 83)⟩ := by decide
    rw [hd]
    have hl : (extend inputs (D_c00.take 23)).getD 83 0 = inputs.getD 83 0 :=
      NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)
    simp only [Def.eval, List.replicate, List.map, Arg.eval, hl]
    exact PipeR14.asm8_self _
  have vsp : HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 84 0 := by
    rw [hE.1 _ _ hsp]
    have h := NativeR14Ret.extend_getD_def inputs D_c00 21 (by decide)
    rw [show inputs.length + 21 = 110 by rw [hlen]; decide] at h
    rw [h]
    have hd : D_c00[21]'(by decide) = ⟨.add, [.id 89, .imm 0x0000000000000020#64]⟩ := by decide
    rw [hd]
    simp only [Def.eval, List.map, Arg.eval]
    have h2 := NativeR14Ret.extend_getD_def inputs (D_c00.take 21) 0 (by decide)
    rw [show inputs.length + 0 = 89 by rw [hlen]; decide] at h2
    rw [h2]
    have hd2 : (D_c00.take 21)[0]'(by decide) = ⟨.add, [.id 84, .imm 0xffffffffffffffe0#64]⟩ := by decide
    rw [hd2]
    simp only [Def.eval, List.map, Arg.eval]
    rw [NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide), op_add, op_add, BitVec.add_assoc,
      show (0xffffffffffffffe0#64 : BitVec 64) + 0x0000000000000020#64 = 0#64 by decide, BitVec.add_zero]
  have x0 := hE.1 _ _ h0
  have S := PipeR14M.spec_c00 inputs (by rw [hlen]; rfl)
  have key : ∀ q ∈ outMemLocs_c00.zip outMem_c00,
      (match q.2 with | some (i, _) => decide (i ∈ PipeR14M.outIds_c00) | none => true) = true := by decide
  have outMap : outMemLocs_c00.map (fun (g, j) => σf.memB g j) = outMem_c00 := by
    have h := outMem_ok_c00
    rw [← hlen, hall] at h
    exact Option.some.inj h
  have outputs := ArmCertPipe.Physical.outMem_end hE _ _ outMap
  have entryLR := ArmCertPipe.Physical.regVal_of_agreesAt
    (r := .x ⟨30, by decide⟩) (i := 83) dp.init.extra hall (by rw [hlen]; decide)
  have entryPC : fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) := by
    rw [pc, entryLR]
    exact (NativeR14Ret.extend_getD_lt _ _ (by rw [hlen]; decide)).symm
  refine ⟨fin, run, ⟨?_, ?_, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, vsp, hz⟩, entryPC⟩
  · exact x0.trans (S 107 (by decide))
  · intro q hq i b hb
    have valid := key q hq
    rw [hb] at valid
    have h := S i (by simpa using valid)
    rw [outputs q hq i b hb]
    simp only [evalDefs] at h
    rw [h]

#print axioms release_fullpc_c00

#check "CURRENT_DECL release_full_c00"
theorem release_full_c00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c00) (hpath : ArmCertPipe.PathOK (extend inputs D_c00) guards_c00) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base) (hp : PinsAgree p rs_c00 forms_c00 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c00 R14Plan.codeWords_c00 R14Plan.entry_c00 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c00 budget bytePA regions_c00 σ0_c00 inputs plan_c00 catalogue capacity_c00 past_c00 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c00.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c00 107 inputs ∧
      (∀ q ∈ outMemLocs_c00.zip outMem_c00, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c00 i inputs) >>> (8 * b)).setWidth 8)) ∧
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
  obtain ⟨fin, run, facts, _⟩ := release_fullpc_c00 real spec config rows mapping table sc bytes b cb
    base ifunc p budget inputs bytePA cs hlen hpath hlr ds hp catalogue entry dp
  exact ⟨fin, run, facts⟩

#print axioms release_full_c00
end ReleaseProfile.DefaultRuntime
