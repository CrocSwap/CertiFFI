import Walk.S1OuterPrefix
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1OuterSplit
abbrev Return := S1OuterBody.Return
abbrev Vars := S1OuterBody.Vars

def info (wp : S1TTWParams) (regime : Regime) (current : TTWState)
    (walkaddr : AddressDescriptor) : TranslationInfo :=
  {regime := regime
   vmid := none
   asid := none
   va := walkaddr.vaddress
   s1level := some current.level
   s2info := none
   s1params := some wp
   s2params := none
   memattrs := walkaddr.memattrs}

noncomputable def resume (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (descaddr : FullAddress) (typ : DescriptorType)
    (skl : BitVec 2) (current : TTWState) (r : S1OuterPrefix.Input) : SailME Return Vars := do
  let (aligned, descaddr, d, typ, fault, _, a64, _, skl, current) ←
    S1WalkSource.named.loop1 wp va regime acc 64 descaddr typ skl current
      r.walkaddr (info wp regime current r.walkaddr) r.aligned r.descriptor r.fault
      r.a64 r.s2fault r.s2fs1mro r.newd
  pure (aligned, descaddr, d, typ, fault, a64, r.s2fs1mro, skl, r.walkaddr, current)

theorem equation (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (startlevel : Int)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64) (typ : DescriptorType)
    (fault : FaultRecord) (a64 s2fs1mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (current : TTWState) :
    S1WalkSource.named.body0 wp va regime acc 64 startlevel
      (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) =
      (S1OuterPrefix.action wp va regime acc startlevel
        (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) >>=
        resume wp va regime acc descaddr typ skl current) := by
  rw [S1OuterBody.equation]
  simp [S1OuterBody.action, S1OuterPrefix.action, resume, info, ← bind_pure_comp, bind_assoc, S1WalkTable.bind_ite]
#print axioms equation
end S1OuterSplit
