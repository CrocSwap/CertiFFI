import Walk.S1WalkTable
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1WalkTable10
abbrev State := S1WalkInvalid.State
abbrev Return := S1WalkInvalid.Return
abbrev Vars := S1WalkInvalid.Vars

def early {α : Type} (fault : FaultRecord) : SailME Return α := do
  let a ← __UNKNOWN_AddressDescriptor ()
  let w ← __UNKNOWN_TTWState ()
  let d ← __UNKNOWN_bits 64
  SailME.throw (fault, a, w, d)

def action (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (d : BitVec 64) (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (current : TTWState) : SailME Return Vars := do
  let next ← AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL10 wp d
  let addr ← AArch64_TTEntryAddress next.level 0#1 0#2 .TGx_4KB wp.txsz va next.baseaddress
  let outOfRange ← AArch64_OAOutOfRange addr.address 0#1 wp.ps .TGx_4KB
  let (fault, newd) ← if outOfRange then do
      early {fault with statuscode := .Fault_AddressSize}
    else pure (fault, if wp.haft == 1#1 then BitVec.update d 10 (Bit 1#1) else d)
  let (aligned, observed, fault, a64, s2fault) ← if newd != d then do
      let _ ← undefined_AddressDescriptor (← occLabel 1607) ()
      let descaccess ← CreateAccDescTTEUpdate acc
      let enabled ← EL2Enabled ()
      let (aligned, descpaddr, a64, s2fault) ← if enabled then do
          let (s2fault, pa) ← AArch64_S2Translate fault walkaddr true (some next.level) true descaccess
          if bne s2fault.statuscode .Fault_None then early s2fault else pure ()
          pure (true, pa, true, s2fault)
        else pure (aligned, walkaddr, a64, s2fault)
      let (fault, observed) ← AArch64_MemSwapTableDesc fault d newd wp.ee descaccess descpaddr ti
      if bne fault.statuscode .Fault_None then early fault else pure ()
      pure (aligned, observed, fault, a64, s2fault)
    else pure (aligned, d, fault, a64, s2fault)
  pure (aligned, addr, observed, .DescriptorType_Table, fault, newd, a64, s2fault, 0#2, next)

theorem equation (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (oldType : DescriptorType) (fault : FaultRecord) (oldNew : BitVec 64)
    (a64 : Bool) (s2fault : FaultRecord) (skl : BitVec 2) (current : TTWState)
    (s : State) (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1)
    (hTG : wp.tgx = .TGx_4KB)
    (hTable : S1DecodeFacts.classify d current.level = .DescriptorType_Table) :
    S1WalkSource.named.body1 wp va .Regime_EL10 acc 64 walkaddr ti s2fs1mro
      (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
      action wp va acc walkaddr ti s2fs1mro aligned d fault a64 s2fault current s := by
  have hdec : AArch64_DecodeDescriptorType d 0#1 0#1 .TGx_4KB current.level =
      (pure .DescriptorType_Table : SailM DescriptorType) := by
    funext t
    rw [S1DecodeFacts.model_eq, hTable]
    rfl
  simp only [S1WalkSource.named.body1, hD128, hDS, hTG, hdec]
  have hReg : ((.Regime_EL10 : Regime) == .Regime_EL10) = true := by decide
  by_cases hHAFT : wp.haft = 1#1 <;>
    simp [action, early, hHAFT, hReg, S1WalkTable.bind_ite, S1WalkTable.map_ite,
      S1WalkTable.map_throw, S1WalkTable.bind_throw, bind_assoc,
      ArmFull.assert, PreSail.assert]
#print axioms equation
end S1WalkTable10
