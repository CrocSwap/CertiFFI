import ArmCertWalk.MemClassStrb
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
namespace NativeEntryBodyMem.Strb
open ArmCertWalk ArmBridge.Draft ArmCertMem.StrbEval
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Strb (post-index) trio (HAND). Success, register result, mem (wfold of the byte) and
StoreEvents from Memory's MemClass.Strb.run (olean 094bee31); ActFrame, NPE (bkHeap), GIC,
PhysicalCount and SP_EL0 from MemClass.Strb.frames; WritesOnly/Separated from
MemClass.Strb.footprint. Memory's premises are threaded through as run
hypotheses; the Rn ≠ Rt guard (WBOVERLAPST) is hRnt. -/
def writes : Effects.Writes := {}

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (current : CurrentS1At spec config rows s)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      domain (MemClass.Strb.query s Rn acc) ∧ (∃ data : S1AccessData spec config rows (MemClass.Strb.query s Rn acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Strb.query s Rn acc) data s) ∧
      MemM1.MemWriteD6.PreW acc s.regs)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hTME : s.regs.FeatureImpl[227] = false)
    (pa : BitVec 56) (mapped : mapping (MemClass.Strb.base s Rn) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 0#2 : SailM Unit) s = .ok () t ∧
      t.regs = (strbPost s Rn imm9).regs ∧
      t.mem = MemM1.MemWriteD1.wfold s.mem pa.toNat 1
        (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (MemClass.Strb.byteOf s Rt)).extractLsb' (8 * j) 8) ∧
      MemClass.Strb.StoreEvents spec (MemClass.Strb.base s Rn) pa s.events MemM1.MemWriteD4.akPlain
        (Sail.BitVec.castWidth (m := 8 * 1) (MemClass.Strb.byteOf s Rt)) t.events ∧
      WritesOnly (fun x => x = pa.toNat) (fun x => s.mem[x]?) (fun x => t.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte (fun x => x = pa.toNat) ∧
      ActFrame s t ∧ t.regs.SP_EL0 = s.regs.SP_EL0 ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.Strb.run spec config rows mapping s imm9 Rn Rt hRn hRt hRnt
    current perAcc mode debug post hEL3A64 hNoEL3A32 hTME pa mapped mmio raw none
  obtain ⟨af, npe, gic, ph, sp⟩ := MemClass.Strb.frames s t imm9 Rn hr
  have fp := MemClass.Strb.footprint spec s.mem pa
    (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (MemClass.Strb.byteOf s Rt)).extractLsb' (8 * j) 8) outside
  rw [← hm] at fp
  have fields : GuardFieldsEq s t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  exact ⟨t, ok, hr, hm, he, fp.1, fp.2, af, sp, Effects.of_scalar writes npe,
    NativeEntryContract.of_scalar af npe gic, quiet_of_fields ticks s t hq fields⟩

#print axioms run
end NativeEntryBodyMem.Strb
