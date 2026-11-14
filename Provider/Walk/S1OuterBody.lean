import Walk.S1ReadAccDesc
import Walk.S1DescriptorRead
import Walk.S1UnknownFault
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option pp.maxSteps 1200
namespace S1OuterBody
abbrev State := S1WalkInvalid.State
abbrev Return := S1WalkInvalid.Return
abbrev Vars := Bool × FullAddress × BitVec 64 × DescriptorType × FaultRecord ×
  Bool × Bool × BitVec 2 × AddressDescriptor × TTWState

noncomputable def action (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (startlevel : Int) : Vars → SailME Return Vars
  | (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current) => do
    let fault := {fault with level := current.level}
    let walkaddr := {walkaddr with paddress := descaddr}
    let walkacc ← CreateAccDescS1TTW (current.level == startlevel) (AArch64_GetVARange va) acc
    let s2fault ← undefined_FaultRecord (← occLabel 1603) ()
    let _ ← undefined_AddressDescriptor (← occLabel 1604) ()
    let enabled ← if regime == .Regime_EL10 then EL2Enabled () else pure false
    let (aligned, d, fault, a64, s2fault, s2fs1mro) ←
      S1DescriptorRead.action enabled aligned a64 s2fs1mro wp.ee fault s2fault
        walkaddr current.level walkacc {
          regime := regime
          vmid := none
          asid := none
          va := walkaddr.vaddress
          s1level := some current.level
          s2info := none
          s1params := some wp
          s2params := none
          memattrs := walkaddr.memattrs}
    if bne fault.statuscode .Fault_None then S1WalkTable10.early fault else pure ()
    let newd ← (Sail.BitVec.castWidth (m := 64) <$>
      undefined_bitvector_at (← occLabel 1605) (Sail.Int.toNatChecked (64 : Int)))
    let (aligned, descaddr, d, typ, fault, _, a64, _, skl, current) ←
      S1WalkSource.named.loop1 wp va regime acc 64 descaddr typ skl current
        walkaddr {
          regime := regime
          vmid := none
          asid := none
          va := walkaddr.vaddress
          s1level := some current.level
          s2info := none
          s1params := some wp
          s2params := none
          memattrs := walkaddr.memattrs}
        aligned d fault a64 s2fault s2fs1mro newd
    pure (aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current)

theorem equation (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (startlevel : Int) (x : Vars) :
    S1WalkSource.named.body0 wp va regime acc 64 startlevel x =
      action wp va regime acc startlevel x := by
  rcases x with ⟨aligned, descaddr, d, typ, fault, a64, s2fs1mro, skl, walkaddr, current⟩
  simp [S1WalkSource.named.body0, action, S1DescriptorRead.action,
    S1WalkTable10.early, S1WalkTable.bind_ite, S1WalkTable.map_ite,
    S1WalkTable.bind_throw, S1WalkTable.map_throw, bind_assoc,
    ArmFull.assert, PreSail.assert]
#print axioms equation
end S1OuterBody
