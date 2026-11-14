import NativeAccess.PairValue
import ArmCertMemPipe.RouteG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace NativeAccess.PairNext
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3 HeapV2StepCerts ArmCertMemPipe

/-- Full next-state facts retained for the caller invariant assembly. -/
def Packet {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (us : List (RegBind.Reg × RegBind.Upd)) (D : Nat → Prop) (Pay : NativeState → NativeState → Prop)
    (x fin : NativeState) : Prop :=
      StepPins fin ∧ HookQuiet (budget - (k + 1)) fin ∧
      CurrentS1At spec config rows (beforeFetchState fin) ∧
      fin.regs._PC = base + offset (k + 1) ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none ∧
      ClosedMembershipAt spec config rows mapping m (beforeFetchState fin) ∧
      MemReloc.ImageOn scope image fin loadBase mapping ∧
      Crypto.BranchV2.BranchPinsV2PA fin ∧ RegBind.Holds us x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      Pay x fin ∧ (∀ a : Nat, (x.mem[a]?).isSome → (fin.mem[a]?).isSome) ∧ SysEq2 x.regs fin.regs

/-- Internal join preserving the full next-state packet from the existing
actual fetch theorem. Concrete instruction dispatchers discharge tail and
transfer arguments; they are not public caller-run obligations. -/
theorem mem_nextG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (RegBind.Reg × RegBind.Upd))
    (next : NativeState → BitVec 64) (X : NativeState → Prop) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (tail : MemTailGAt real spec config rows (GCtx spec config rows mapping m X) D w writes K x (next x) us Pay)
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      StepPins fin ∧ HookQuiet (budget - (k + 1)) fin ∧
      CurrentS1At spec config rows (beforeFetchState fin) ∧
      fin.regs._PC = base + offset (k + 1) ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none ∧
      ClosedMembershipAt spec config rows mapping m (beforeFetchState fin) ∧
      MemReloc.ImageOn scope image fin loadBase mapping ∧
      Crypto.BranchV2.BranchPinsV2PA fin ∧ RegBind.Holds us x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      Pay x fin ∧ (∀ a : Nat, (x.mem[a]?).isSome → (fin.mem[a]?).isSome) ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact entry_mem_nextG real spec config rows mapping w writes K x inv.v2.v1.pins (next x) (offset (k + 1)) us m X D Pay
      tail inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page
      aligned nextPlaced inv.v2.v1.current inv.v2.closed scope image loadBase inv.v2.placed separated codeD
      inv.v2.branch inv.raw inv.noUpd xferX xferPay inv.post2 inv.mode inv.debug inv.feat inv.dcache
      obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
      obligations.perAcc obligations.code

#print axioms mem_nextG
end NativeAccess.PairNext
