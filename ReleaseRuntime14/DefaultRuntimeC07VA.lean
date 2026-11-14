-- Current-profile roots and typed back-derivations.
import DefaultRuntimeC07Roots
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
#check "CURRENT_DECL release_full_c07"
theorem release_full_c07
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
    (hlen : inputs.length = n0_c07)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (st : PipeR14.Physical.DataStartsR14 mapping p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 (PipeR14.AccessAnchors.sites_c07 p) sc base)
    (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (PipeR14.AccessAnchors.bytePA_c07 p mapping) regions_c07 σ0_c07 inputs plan_c07 catalogue capacity_c07 past_c07 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c07.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c07 69 inputs ∧
      (∀ q ∈ outMemLocs_c07.zip outMem_c07, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte (PipeR14.AccessAnchors.bytePA_c07 p mapping) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c07 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 87 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 88 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 89 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 90 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 91 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 92 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 93 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 94 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 95 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 96 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 97 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 98 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 99 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 100 0 ∧
      fin.regs._Z = entry.regs._Z :=
  ReleaseProfile.DefaultRuntime.release_full_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs (PipeR14.AccessAnchors.bytePA_c07 p mapping) cs hlen hpath hlr (PipeR14.Physical.dataStatic_c07 st dp.init.core.closed dp.init.core.v1.current.images.topology) hp catalogue entry dp

#print axioms release_full_c07

#check "CURRENT_DECL release_fullpc_c07"
theorem release_fullpc_c07
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
    (hlen : inputs.length = n0_c07)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (st : PipeR14.Physical.DataStartsR14 mapping p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 (PipeR14.AccessAnchors.sites_c07 p) sc base)
    (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (PipeR14.AccessAnchors.bytePA_c07 p mapping) regions_c07 σ0_c07 inputs plan_c07 catalogue capacity_c07 past_c07 entry) :
    ∃ fin, modelStep real (stateAt real entry (plan_c07.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c07 69 inputs ∧
      (∀ q ∈ outMemLocs_c07.zip outMem_c07, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte (PipeR14.AccessAnchors.bytePA_c07 p mapping) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c07 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 87 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 88 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 89 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 90 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 91 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 92 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 93 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 94 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 95 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 96 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 97 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 98 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 99 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 100 0 ∧
      fin.regs._Z = entry.regs._Z) ∧
      fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) :=
  ReleaseProfile.DefaultRuntime.release_fullpc_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs (PipeR14.AccessAnchors.bytePA_c07 p mapping) cs hlen hpath hlr (PipeR14.Physical.dataStatic_c07 st dp.init.core.closed dp.init.core.v1.current.images.topology) hp catalogue entry dp

#print axioms release_fullpc_c07

#check "CURRENT_DECL release_ct_c07"
theorem release_ct_c07
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
    (st : PipeR14.Physical.DataStartsR14 mapping p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 (PipeR14.AccessAnchors.sites_c07 p) sc base)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c07)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c07) guards_c07)
    (hlr1 : (inputs1.getD 99 0).toNat < 2 ^ 54)
    (hp1 : PinsAgree p rs_c07 forms_c07 inputs1)
    (entry1 : NativeState)
    (dp1 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (PipeR14.AccessAnchors.bytePA_c07 p mapping) regions_c07 σ0_c07 inputs1 plan_c07 catalogue1 capacity_c07 past_c07 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c07)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c07) guards_c07)
    (hlr2 : (inputs2.getD 99 0).toNat < 2 ^ 54)
    (hp2 : PinsAgree p rs_c07 forms_c07 inputs2)
    (entry2 : NativeState)
    (dp2 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (PipeR14.AccessAnchors.bytePA_c07 p mapping) regions_c07 σ0_c07 inputs2 plan_c07 catalogue2 capacity_c07 past_c07 entry2)
    (hlr12 : inputs1.getD 99 0 = inputs2.getD 99 0) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c07.length) (stateAt real entry2 plan_c07.length) :=
  ReleaseProfile.DefaultRuntime.release_ct_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget (PipeR14.AccessAnchors.bytePA_c07 p mapping) cs (PipeR14.Physical.dataStatic_c07 st dp1.init.core.closed dp1.init.core.v1.current.images.topology) nodup catalogue1 catalogue2 inputs1 hlen1 hpath1 hlr1 hp1 entry1 dp1 inputs2 hlen2 hpath2 hlr2 hp2 entry2 dp2 hlr12

#print axioms release_ct_c07

end ReleaseProfile.DefaultRuntimeAnchored

namespace ReleaseProfile.DefaultRuntimeVA
#check "CURRENT_DECL release_full_c07"
theorem release_full_c07
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
    (hlen : inputs.length = n0_c07)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (st : PipeR14.Physical.DataStartsR14 mapping p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 (PipeR14.AccessAnchors.sites_c07 p) sc base)
    (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (pinv p) regions_c07 σ0_c07 inputs plan_c07 catalogue capacity_c07 past_c07 entry)
    (view : ViewAgree_c07 p mapping) :
    ∃ fin, modelStep real (stateAt real entry (plan_c07.length - 1)) = .ok () fin ∧
      HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c07 69 inputs ∧
      (∀ q ∈ outMemLocs_c07.zip outMem_c07, ∀ i b, q.2 = some (i, b) →
        regionByte mapping (pinv p) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c07 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 87 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 88 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 89 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 90 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 91 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 92 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 93 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 94 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 95 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 96 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 97 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 98 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 99 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 100 0 ∧
      fin.regs._Z = entry.regs._Z := by
  obtain ⟨fin, hs, hx, hm, rest⟩ := ReleaseProfile.DefaultRuntimeAnchored.release_full_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs cs hlen hpath hlr st hp catalogue entry (dp.anchored nodup view.1)
  exact ⟨fin, hs, hx, fun q hq i b hb => by
    show (mapping _).bind _ = _
    rw [← view.2 q hq i b hb]; exact hm q hq i b hb, rest⟩

#print axioms release_full_c07

#check "CURRENT_DECL release_fullpc_c07"
theorem release_fullpc_c07
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
    (hlen : inputs.length = n0_c07)
    (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07)
    (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (st : PipeR14.Physical.DataStartsR14 mapping p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 (PipeR14.AccessAnchors.sites_c07 p) sc base)
    (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState)
    (dp : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (pinv p) regions_c07 σ0_c07 inputs plan_c07 catalogue capacity_c07 past_c07 entry)
    (view : ViewAgree_c07 p mapping) :
    ∃ fin, modelStep real (stateAt real entry (plan_c07.length - 1)) = .ok () fin ∧
      (HeapV2StepCerts.RegBind.regVal fin (.x 0) = PipeR14M.specVal_c07 69 inputs ∧
      (∀ q ∈ outMemLocs_c07.zip outMem_c07, ∀ i b, q.2 = some (i, b) →
        regionByte mapping (pinv p) fin q.1.1 q.1.2 = some (((PipeR14M.specVal_c07 i inputs) >>> (8 * b)).setWidth 8)) ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨18, by decide⟩) = inputs.getD 87 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨19, by decide⟩) = inputs.getD 88 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨20, by decide⟩) = inputs.getD 89 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨21, by decide⟩) = inputs.getD 90 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨22, by decide⟩) = inputs.getD 91 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨23, by decide⟩) = inputs.getD 92 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨24, by decide⟩) = inputs.getD 93 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨25, by decide⟩) = inputs.getD 94 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨26, by decide⟩) = inputs.getD 95 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨27, by decide⟩) = inputs.getD 96 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨28, by decide⟩) = inputs.getD 97 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨29, by decide⟩) = inputs.getD 98 0 ∧
      HeapV2StepCerts.RegBind.regVal fin (.x ⟨30, by decide⟩) = inputs.getD 99 0 ∧
      HeapV2StepCerts.RegBind.regVal fin .sp = inputs.getD 100 0 ∧
      fin.regs._Z = entry.regs._Z) ∧
      fin.regs._PC = HeapV2StepCerts.RegBind.regVal entry (.x ⟨30, by decide⟩) := by
  obtain ⟨fin, hs, ⟨hx, hm, rest⟩, pc⟩ := ReleaseProfile.DefaultRuntimeAnchored.release_fullpc_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs cs hlen hpath hlr st hp catalogue entry (dp.anchored nodup view.1)
  exact ⟨fin, hs, ⟨hx, fun q hq i b hb => by
    show (mapping _).bind _ = _
    rw [← view.2 q hq i b hb]; exact hm q hq i b hb, rest⟩, pc⟩

#print axioms release_fullpc_c07

#check "CURRENT_DECL release_ct_c07"
theorem release_ct_c07
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
    (st : PipeR14.Physical.DataStartsR14 mapping p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 (PipeR14.AccessAnchors.sites_c07 p) sc base)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c07)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c07) guards_c07)
    (hlr1 : (inputs1.getD 99 0).toNat < 2 ^ 54)
    (hp1 : PinsAgree p rs_c07 forms_c07 inputs1)
    (entry1 : NativeState)
    (dp1 : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (pinv p) regions_c07 σ0_c07 inputs1 plan_c07 catalogue1 capacity_c07 past_c07 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c07)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c07) guards_c07)
    (hlr2 : (inputs2.getD 99 0).toNat < 2 ^ 54)
    (hp2 : PinsAgree p rs_c07 forms_c07 inputs2)
    (entry2 : NativeState)
    (dp2 : VADeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c07 budget (pinv p) regions_c07 σ0_c07 inputs2 plan_c07 catalogue2 capacity_c07 past_c07 entry2)
    (hlr12 : inputs1.getD 99 0 = inputs2.getD 99 0)
    (view : ViewAgree_c07 p mapping) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c07.length) (stateAt real entry2 plan_c07.length) := by
  exact ReleaseProfile.DefaultRuntimeAnchored.release_ct_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget cs st nodup catalogue1 catalogue2 inputs1 hlen1 hpath1 hlr1 hp1 entry1 (dp1.anchored nodup view.1) inputs2 hlen2 hpath2 hlr2 hp2 entry2 (dp2.anchored nodup view.1) hlr12

#print axioms release_ct_c07

end ReleaseProfile.DefaultRuntimeVA

