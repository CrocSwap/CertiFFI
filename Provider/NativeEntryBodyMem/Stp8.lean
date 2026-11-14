import ArmCertWalk.MemClassStp8
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
namespace NativeEntryBodyMem.Stp8
open ArmCertWalk ArmBridge.Draft
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Stp8 (Rn base, signed offset, 64-bit pair, 8-aligned general form) trio (HAND).
Success, registers unchanged, mem (two 8-byte wfolds) and PairEvents (one LSE2 16-byte
access if 16-aligned, else two 8-byte halves each with its own translation) from Memory's
MemClass.Stp8.run; frames from MemClass.Stp8.frames; WritesOnly/Separated over the two
windows from MemClass.Stp8.footprint. Memory's premises are threaded through as run
hypotheses. In HeapV2 the base x0 is only 8-aligned (entry tst x0,#7). -/
def writes : Effects.Writes := {}

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (current : CurrentS1At spec config rows s)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      PairAccess spec config rows mapping (MemClass.Stp8.pairAddr s Rn imm7) acc s)
    (preW : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc → MemM1.MemWriteD6.PreW acc s.regs)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hTME : s.regs.FeatureImpl[227] = false) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (h8 : (MemClass.Stp8.pairAddr s Rn imm7).toNat % 8 = 0)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping (MemClass.Stp8.pairAddr s Rn imm7) = some pa1.toNat)
    (mapped2 : mapping (plus8 (MemClass.Stp8.pairAddr s Rn imm7)) = some pa2.toNat)
    (contiguous : (MemClass.Stp8.pairAddr s Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (outside2 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa2.toNat + i))
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) s = .ok () t ∧
      t.regs = s.regs ∧
      t.mem = MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold s.mem pa1.toNat 8 (fun j => (ArmCertMem.StpEval.stpData s Rt Rt2).extractLsb' (8 * j) 8)) pa2.toNat 8 (fun j => (ArmCertMem.StpEval.stpData s Rt Rt2).extractLsb' (8 * (j + 8)) 8) ∧
      PairEvents spec (MemClass.Stp8.pairAddr s Rn imm7) pa1 pa2
        (.memWrite pa1.toNat 16 (some (MemClass.Stp8.pairAddr s Rn imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (ArmCertMem.StpEval.stpData s Rt Rt2))) none)
        (.memWrite pa1.toNat 8 (some (MemClass.Stp8.pairAddr s Rn imm7).toNat) MemM1.MemWriteD4.akPlain
          (some ((ArmCertMem.StpEval.stpData s Rt Rt2).extractLsb' 0 64)) none)
        (.memWrite pa2.toNat 8 (some (plus8 (MemClass.Stp8.pairAddr s Rn imm7)).toNat) MemM1.MemWriteD4.akPlain
          (some ((ArmCertMem.StpEval.stpData s Rt Rt2).extractLsb' 64 64)) none)
        s.events t.events ∧
      WritesOnly (fun x => (pa1.toNat ≤ x ∧ x < pa1.toNat + 8) ∨ (pa2.toNat ≤ x ∧ x < pa2.toNat + 8)) (fun x => s.mem[x]?) (fun x => t.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte (fun x => (pa1.toNat ≤ x ∧ x < pa1.toNat + 8) ∨ (pa2.toNat ≤ x ∧ x < pa2.toNat + 8)) ∧
      ActFrame s t ∧ t.regs.SP_EL0 = s.regs.SP_EL0 ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.Stp8.run spec config rows mapping s imm7 Rn Rt Rt2 hRn hRt hRt2
    current perAcc preW mode debug post hEL3A64 hNoEL3A32 hTME lse2 dcache h8 pa1 pa2 mapped1 mapped2
    contiguous mmio1 mmio2 outside1 raw noUpd
  obtain ⟨af, npe, gic, ph, sp⟩ := MemClass.Stp8.frames s t hr
  have fp := MemClass.Stp8.footprint spec s.mem pa1 pa2 (fun j => (ArmCertMem.StpEval.stpData s Rt Rt2).extractLsb' (8 * j) 8)
    (fun j => (ArmCertMem.StpEval.stpData s Rt Rt2).extractLsb' (8 * (j + 8)) 8) outside1 outside2
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
end NativeEntryBodyMem.Stp8
