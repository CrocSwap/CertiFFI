-- Current-profile roots and typed back-derivations.
import DefaultRuntimeC08Roots
import DefaultRuntimeVAEntry
import ReleaseR14.VA

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open PipeR14 ReleaseProfile.DefaultRuntime ReleaseR14.VA
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntimeAnchored
#check "CURRENT_DECL release_full_c08"
theorem release_full_c08
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
    (inputs : List (BitVec 64))
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c08)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (PipeR14.AccessAnchors.bytePA_c08 p mapping) regions_c08 σ0_c08 inputs plan_c08 catalogue capacity_c08 past_c08 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c08 0 inputs ∧
      (∀ q ∈ outMemLocs_c08.zip outMem_c08, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte (PipeR14.AccessAnchors.bytePA_c08 p mapping) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c08 i inputs) >>> (8 * b)).setWidth 8)) ∧
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
      fin.regs.PSTATE.V.setWidth 64 = inputs.getD 35 0 :=
  ReleaseProfile.DefaultRuntime.release_full_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs (PipeR14.AccessAnchors.bytePA_c08 p mapping) cs hlen hpath catalogue entry dp

#print axioms release_full_c08

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
    (inputs : List (BitVec 64))
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c08)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (PipeR14.AccessAnchors.bytePA_c08 p mapping) regions_c08 σ0_c08 inputs plan_c08 catalogue capacity_c08 past_c08 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c08 0 inputs ∧
      (∀ q ∈ outMemLocs_c08.zip outMem_c08, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte (PipeR14.AccessAnchors.bytePA_c08 p mapping) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c08 i inputs) >>> (8 * b)).setWidth 8)) ∧
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
      fin.regs._PC = base + BitVec.ofNat 64 0x2baa78 :=
  ReleaseProfile.DefaultRuntime.release_fullpc_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs (PipeR14.AccessAnchors.bytePA_c08 p mapping) cs hlen hpath catalogue entry dp

#print axioms release_fullpc_c08

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
    (budget : Nat)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c08)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c08) guards_c08)
    (entry1 : NativeState)
    (dp1 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (PipeR14.AccessAnchors.bytePA_c08 p mapping) regions_c08 σ0_c08 inputs1 plan_c08 catalogue1 capacity_c08 past_c08 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c08)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c08) guards_c08)
    (entry2 : NativeState)
    (dp2 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (PipeR14.AccessAnchors.bytePA_c08 p mapping) regions_c08 σ0_c08 inputs2 plan_c08 catalogue2 capacity_c08 past_c08 entry2) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c08.length) (stateAt real entry2 plan_c08.length) :=
  ReleaseProfile.DefaultRuntime.release_ct_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget (PipeR14.AccessAnchors.bytePA_c08 p mapping) cs nodup catalogue1 catalogue2 inputs1 hlen1 hpath1 entry1 dp1 inputs2 hlen2 hpath2 entry2 dp2

#print axioms release_ct_c08

end ReleaseProfile.DefaultRuntimeAnchored

namespace ReleaseProfile.DefaultRuntimeVA
#check "CURRENT_DECL release_full_c08"
theorem release_full_c08
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
    (inputs : List (BitVec 64))
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c08)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (pinv p) regions_c08 σ0_c08 inputs plan_c08 catalogue capacity_c08 past_c08 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c08 0 inputs ∧
      (∀ q ∈ outMemLocs_c08.zip outMem_c08, ∀ i b, q.2 = some (i, b) →
        regionByte mapping (pinv p) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c08 i inputs) >>> (8 * b)).setWidth 8)) ∧
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
  obtain ⟨fin, hs, hx, hm, rest⟩ := ReleaseProfile.DefaultRuntimeAnchored.release_full_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs cs hlen hpath catalogue entry (dp.anchored nodup (viewAgree_c08 p mapping).1)
  exact ⟨fin, hs, hx, fun q hq i b hb => by
    show (mapping _).bind _ = _
    rw [← (viewAgree_c08 p mapping).2 q hq i b hb]; exact hm q hq i b hb, rest⟩

#print axioms release_full_c08

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
    (inputs : List (BitVec 64))
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (hlen : inputs.length = n0_c08)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (pinv p) regions_c08 σ0_c08 inputs plan_c08 catalogue capacity_c08 past_c08 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c08.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c08 0 inputs ∧
      (∀ q ∈ outMemLocs_c08.zip outMem_c08, ∀ i b, q.2 = some (i, b) →
        regionByte mapping (pinv p) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c08 i inputs) >>> (8 * b)).setWidth 8)) ∧
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
  obtain ⟨fin, hs, ⟨hx, hm, rest⟩, pc⟩ := ReleaseProfile.DefaultRuntimeAnchored.release_fullpc_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs cs hlen hpath catalogue entry (dp.anchored nodup (viewAgree_c08 p mapping).1)
  exact ⟨fin, hs, ⟨hx, fun q hq i b hb => by
    show (mapping _).bind _ = _
    rw [← (viewAgree_c08 p mapping).2 q hq i b hb]; exact hm q hq i b hb, rest⟩, pc⟩

#print axioms release_fullpc_c08

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
    (budget : Nat)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c08)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c08) guards_c08)
    (entry1 : NativeState)
    (dp1 : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (pinv p) regions_c08 σ0_c08 inputs1 plan_c08 catalogue1 capacity_c08 past_c08 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c08)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c08) guards_c08)
    (entry2 : NativeState)
    (dp2 : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c08 budget (pinv p) regions_c08 σ0_c08 inputs2 plan_c08 catalogue2 capacity_c08 past_c08 entry2) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c08.length) (stateAt real entry2 plan_c08.length) := by
  exact ReleaseProfile.DefaultRuntimeAnchored.release_ct_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget cs nodup catalogue1 catalogue2 inputs1 hlen1 hpath1 entry1 (dp1.anchored nodup (viewAgree_c08 p mapping).1) inputs2 hlen2 hpath2 entry2 (dp2.anchored nodup (viewAgree_c08 p mapping).1)

#print axioms release_ct_c08

end ReleaseProfile.DefaultRuntimeVA

