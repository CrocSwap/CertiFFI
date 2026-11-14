import ArmCertWalk.MemClassLdrb
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
namespace NativeEntryBodyMem.Ldrb
open ArmCertWalk ArmBridge.Draft ArmCertMem.LdrbEval
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Ldrb (post-index) trio (HAND). Success, register result, mem and LoadEvents from
Memory's MemClass.Ldrb.run (olean c3c19628); ActFrame, NPE (bkHeap), GIC, PhysicalCount
and SP_EL0 from MemClass.Ldrb.frames. Memory's premises are threaded through as run
hypotheses; the Rn ≠ Rt guard (WBOVERLAPLD) is hRnt. -/
def writes : Effects.Writes := {}

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (current : CurrentS1At spec config rows s)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (MemClass.Ldrb.query s Rn acc) ∧ ∃ data : S1AccessData spec config rows (MemClass.Ldrb.query s Rn acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldrb.query s Rn acc) data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hTME : s.regs.FeatureImpl[227] = false) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping (MemClass.Ldrb.base s Rn) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (v : BitVec 8) (byte : s.mem[pa.toNat]? = some v)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) s = .ok () t ∧
      t.regs = (ldrbPost s Rn Rt imm9 v).regs ∧ t.mem = s.mem ∧
      MemClass.Ldrb.LoadEvents spec (MemClass.Ldrb.base s Rn) pa s.events
        (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) t.events ∧
      ActFrame s t ∧ t.regs.SP_EL0 = s.regs.SP_EL0 ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.Ldrb.run spec config rows mapping s imm9 Rn Rt hRn hRt hRnt
    current perAcc mode debug post hEL3A64 hNoEL3A32 hTME dcache pa mapped mmio v byte outside raw none
  obtain ⟨af, npe, gic, ph, sp⟩ := MemClass.Ldrb.frames s t imm9 Rn Rt v hr
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
  exact ⟨t, ok, hr, hm, he, af, sp, Effects.of_scalar writes npe, NativeEntryContract.of_scalar af npe gic,
    quiet_of_fields ticks s t hq fields⟩

#print axioms run
end NativeEntryBodyMem.Ldrb
