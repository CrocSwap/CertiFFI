import HeapControl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.ClosedTransport

theorem access {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : ArmCertWalk.State}
    (access : CurrentS1AccessAt spec config rows mapping query data before)
    (controls : RtPremC.ctlv after.regs = RtPremC.ctlv before.regs) :
    CurrentS1AccessAt spec config rows mapping query data after := by
  simp only [RtPremC.ctlv, Prod.mk.injEq] at controls
  rcases controls with ⟨features,el,nrw,tlb,⟨tcr,tcr2,hcr,scr,sctlr,mair,httbr,pir,pire,por⟩,
    ⟨ttbr0,ttbr1⟩,pa,bbm⟩
  exact current_s1_access_registers access features tcr sctlr ttbr0 httbr ttbr1 (fun _ _ => bbm)

theorem closed {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {before after : ArmCertWalk.State}
    (c : ClosedMembershipAt spec config rows mapping m before)
    (controls : RtPremC.ctlv after.regs = RtPremC.ctlv before.regs) :
    ClosedMembershipAt spec config rows mapping m after := by
  intro va acc aligned size permitted
  obtain ⟨q,hva,hraw,hal,hsize,member,data,current⟩ := c va acc aligned size permitted
  exact ⟨q,hva,hraw,hal,hsize,member,data,access current controls⟩

theorem before_fetch (s : NativeState) : RtPremC.ctlv (beforeFetchState s).regs = RtPremC.ctlv s.regs := by
  simp (disch := decide) only [RtPremC.ctlv, beforeFetchState, RegMap.set_ne]

#print axioms access
#print axioms closed
#print axioms before_fetch
end DitShim243.ClosedTransport
