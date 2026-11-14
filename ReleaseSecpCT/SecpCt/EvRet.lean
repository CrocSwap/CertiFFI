-- secp CT0: single-run event shape of the secp body's terminal RET (X30) over TranslateSpan.DefaultMTE2.Core
-- (same inputs as TranslateSpan.DefaultRet.terminal), via Runtime14 DefaultHeapShimControl.shim_ret (MTE2 CurrentInv) at the
-- patched offset `fun j => if j = k + 1 then X30 - base else offset j` (CurrentInv reads the offset only through pc = base + offset k).
import DefaultHeapShimControl
import TranslateSpan.DefaultRet
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace SecpCt

theorem ev_ret (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : NativeMteTagCheck.ControlCatalogue) (x : NativeState)
    (core : TranslateSpan.DefaultMTE2.Core spec config rows mapping m scope image loadBase base offset budget profile catalogue k x)
    (branch : TranslateSpan.BranchMTE2.Pins x) (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (low : (x.regs.gpr[30]).toNat < 2 ^ 55)
    (fetch : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping [] x fin := by
  let off : Nat → BitVec 64 := fun j => if j = k + 1 then x.regs.gpr[30] - base else offset j
  have offK : off k = offset k := by simp only [off, if_neg (Nat.ne_of_lt (Nat.lt_succ_self k))]
  have offK1 : off (k + 1) = x.regs.gpr[30] - base := by simp only [off, if_pos rfl]
  have inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base off budget k
      catalogue x :=
    ⟨⟨core.v1.pins, core.v1.features, core.v1.debug, core.v1.current, core.v1.quiet, core.v1.gic,
        by rw [offK]; exact core.v1.pc⟩,
      core.closed, core.placed, branch, core.raw, core.noUpd, core.post, core.mode, core.debug, core.feat, core.dcache,
      core.controls⟩
  obtain ⟨fin, run, _, _, _, _, _, ev, _⟩ :=
    ReleaseProfile.DefaultHeapShimControl.shim_ret real spec config rows mapping m scope image loadBase separated
      base off budget k catalogue room page (by rw [offK]; exact aligned) nodup x inv low
      (by rw [offK1, BitVec.add_comm, BitVec.sub_add_cancel]) fetch
  exact ⟨fin, run, ev⟩

end SecpCt
#print axioms SecpCt.ev_ret
