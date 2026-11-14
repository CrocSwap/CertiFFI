import ArmCertWalk.MemClassStp
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
namespace NativeEntryBodyMem.Stp
open ArmCertWalk ArmBridge.Draft ArmCertMem.StpEval
open ArmCertMem.LdpEval (ldpAddr)
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Stp (SP base, signed offset, 64-bit pair) trio (HAND). Success, registers unchanged,
mem (16-byte wfold) and NoUpdateTraffic + memWrite from Memory's MemClass.Stp.run; frames
from MemClass.Stp.frames; WritesOnly/Separated over [pa, pa+16) from MemClass.Stp.footprint.
Memory's premises are threaded through as run hypotheses. -/
def writes : Effects.Writes := {}

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (current : CurrentS1At spec config rows s)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      domain (MemClass.Stp.query s imm7 acc) ∧ (∃ data : S1AccessData spec config rows (MemClass.Stp.query s imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query s imm7 acc) data s) ∧
      MemM1.MemWriteD6.PreW acc s.regs)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hTME : s.regs.FeatureImpl[227] = false) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (hsp : s.regs.SP_EL0.toNat % 16 = 0) (hal : (ldpAddr s imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ldpAddr s imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i))
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2 : SailM Unit) s = .ok () t ∧
      t.regs = s.regs ∧ t.mem = MemM1.MemWriteD1.wfold s.mem pa.toNat 16 (MemM1.MemWriteD4.wbyte (stpData s Rt Rt2)) ∧
      (∃ ad mid, NoUpdateTraffic spec (ldpAddr s imm7) s.events ad mid ∧
        t.events = mid.push (.memWrite pa.toNat 16 (some (ldpAddr s imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (stpData s Rt Rt2))) none)) ∧
      WritesOnly (fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16) (fun x => s.mem[x]?) (fun x => t.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte (fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16) ∧
      ActFrame s t ∧ t.regs.SP_EL0 = s.regs.SP_EL0 ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.Stp.run spec config rows mapping s imm7 Rt Rt2 hRt hRt2
    current perAcc mode debug post hEL3A64 hNoEL3A32 hTME lse2 dcache hsp hal pa mapped mmio raw noUpd
  obtain ⟨af, npe, gic, ph, sp⟩ := MemClass.Stp.frames s t hr
  have fp := MemClass.Stp.footprint spec s.mem pa (MemM1.MemWriteD4.wbyte (stpData s Rt Rt2)) outside
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
end NativeEntryBodyMem.Stp
