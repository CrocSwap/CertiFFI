import ArmCertWalk.MemClassLdp
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
namespace NativeEntryBodyMem.Ldp
open ArmCertWalk ArmBridge.Draft ArmCertMem.LdpEval
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Ldp (SP base, signed offset, 64-bit pair) trio (HAND). Success, register result
(ldpPost), mem unchanged and NoUpdateTraffic + memRead from Memory's MemClass.Ldp.run;
frames from MemClass.Ldp.frames. Memory's premises are threaded through as run hypotheses;
the Rt ≠ Rt2 guard (LDP UNPREDICTABLE) is hRtt. -/
def writes : Effects.Writes := {}

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (hRtt : Rt ≠ Rt2)
    (current : CurrentS1At spec config rows s)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (MemClass.Ldp.query s imm7 acc) ∧ ∃ data : S1AccessData spec config rows (MemClass.Ldp.query s imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldp.query s imm7 acc) data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : MemM1.MemReadD2.PostRegs2 s.regs)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hTME : s.regs.FeatureImpl[227] = false) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (hsp : s.regs.SP_EL0.toNat % 16 = 0) (hal : (ldpAddr s imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ldpAddr s imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec 128) (bytes : ∀ i < 16, s.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2 : SailM Unit) s = .ok () t ∧
      t.regs = (ldpPost s Rt Rt2 data).regs ∧ t.mem = s.mem ∧
      (∃ ad mid, NoUpdateTraffic spec (ldpAddr s imm7) s.events ad mid ∧
        t.events = mid.push (.memRead pa.toNat 16 (some (ldpAddr s imm7).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)) ∧
      ActFrame s t ∧ t.regs.SP_EL0 = s.regs.SP_EL0 ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.Ldp.run spec config rows mapping s imm7 Rt Rt2 hRt hRt2 hRtt
    current perAcc mode debug post hEL3A64 hNoEL3A32 hTME lse2 dcache hsp hal pa mapped mmio data bytes raw noUpd
  obtain ⟨af, npe, gic, ph, sp⟩ := MemClass.Ldp.frames s t Rt Rt2 data hr
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
  exact ⟨t, ok, hr, hm, he, af, sp, Effects.of_scalar writes npe,
    NativeEntryContract.of_scalar af npe gic, quiet_of_fields ticks s t hq fields⟩

#print axioms run
end NativeEntryBodyMem.Ldp
