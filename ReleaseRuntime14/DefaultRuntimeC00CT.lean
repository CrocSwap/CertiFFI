-- event-trace equality and final PC for the same checked c00 deployment.
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
#check "CURRENT_DECL release_ct_c00"
theorem release_ct_c00
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
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (catalogue1 catalogue2 : NativeMteTagCheck.ControlCatalogue)
    (inputs1 : List (BitVec 64))
    (hlen1 : inputs1.length = n0_c00)
    (hpath1 : ArmCertPipe.PathOK (extend inputs1 D_c00) guards_c00)
    (hlr1 : (inputs1.getD 83 0).toNat < 2 ^ 54)
    (hp1 : PinsAgree p rs_c00 forms_c00 inputs1)
    (entry1 : NativeState)
    (dp1 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c00 R14Plan.codeWords_c00 R14Plan.entry_c00 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c00 budget bytePA regions_c00 σ0_c00 inputs1 plan_c00 catalogue1 capacity_c00 past_c00 entry1)
    (inputs2 : List (BitVec 64))
    (hlen2 : inputs2.length = n0_c00)
    (hpath2 : ArmCertPipe.PathOK (extend inputs2 D_c00) guards_c00)
    (hlr2 : (inputs2.getD 83 0).toNat < 2 ^ 54)
    (hp2 : PinsAgree p rs_c00 forms_c00 inputs2)
    (entry2 : NativeState)
    (dp2 : DeploymentPremises spec config rows mapping
      (R14E17.consumerMap R14Plan.accesses_c00 R14Plan.codeWords_c00 R14Plan.entry_c00 p base.toNat mapping table)
      sc (referenceImageI bytes base ifunc) base base offset_c00 budget bytePA regions_c00 σ0_c00 inputs2 plan_c00 catalogue2 capacity_c00 past_c00 entry2)
    (hlr12 : inputs1.getD 83 0 = inputs2.getD 83 0) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 plan_c00.length) (stateAt real entry2 plan_c00.length) := by
  obtain ⟨inv1, fin1, run1, _, pc1, _, ev1⟩ :=
    run_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
      dp1.page dp1.low hlen1 hpath1 hlr1 ds hp1 catalogue1 nodup dp1.room entry1 dp1.init
  obtain ⟨inv2, fin2, run2, _, pc2, _, ev2⟩ :=
    run_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
      dp2.page dp2.low hlen2 hpath2 hlr2 ds hp2 catalogue2 nodup dp2.room entry2 dp2.init
  have len : plan_c00.length = 21 := rfl
  have hL : 0 < plan_c00.length := by omega
  refine PhasedCT.phased_records (stateAt real entry1) (stateAt real entry2)
    (fun _ _ _ => True) plan_c00.length trivial
    (by rw [(inv1 0 hL).core.v1.pc, (inv2 0 hL).core.v1.pc]) ?_
  intro k hk _
  have pc : (stateAt real entry1 k).regs._PC = (stateAt real entry2 k).regs._PC := by
    rw [(inv1 k hk).core.v1.pc, (inv2 k hk).core.v1.pc]
  refine ⟨?_, trivial⟩
  by_cases earlier : k + 1 < plan_c00.length
  · obtain ⟨f1, r1, n1, _, _, e1⟩ :=
      steps_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs1 bytePA cs
        dp1.page dp1.low hlen1 hpath1 hlr1 ds hp1 catalogue1 entry1 nodup dp1.room k earlier _ (inv1 k hk)
    obtain ⟨f2, r2, n2, _, _, e2⟩ :=
      steps_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs2 bytePA cs
        dp2.page dp2.low hlen2 hpath2 hlr2 ds hp2 catalogue2 entry2 nodup dp2.room k earlier _ (inv2 k hk)
    rw [ArmCertValue.Physical.stateAt_succ_of' r1, ArmCertValue.Physical.stateAt_succ_of' r2]
    exact StepEvents.pair spec mapping (records_c00 spec p k) _ _ _ _ e1 e2 pc
      (by rw [n1.core.v1.pc, n2.core.v1.pc])
  · have last : k = plan_c00.length - 1 := by omega
    subst k
    rw [ArmCertValue.Physical.stateAt_succ_of' run1, ArmCertValue.Physical.stateAt_succ_of' run2]
    exact StepEvents.pair spec mapping [] _ _ _ _ ev1 ev2 pc (pc1.trans (hlr12.trans pc2.symm))

#print axioms release_ct_c00
end ReleaseProfile.DefaultRuntime
