import ArmCertMemPipe.TailELdrU32
import ArmCertMemPipe.TailLdrU32
import HeapV2StepCerts.MemTailD
import ArmCertMemPipe.TailELdpOff
import ArmCertMemPipe.TailEStpOff
import DefaultRuntimeReadFour
import DefaultRuntimeLdrU64
import DefaultRuntimeLdrU64Sp
import DefaultRuntimeLdrbU
import DefaultRuntimeLdpPost
import DefaultRuntimeLdpOffset
import DefaultRuntimeStrU32
import DefaultRuntimeStrU64Sp
import DefaultRuntimeStrbU
import DefaultRuntimeStpPre
import DefaultRuntimeStpOffset
-- Actual MTE2-on runtime memory tails with ordered events.
import ArmCertMemPipe.TailELdrU64
import ArmCertMemPipe.TailELdrU64Sp
import ArmCertMemPipe.TailELdrbU
import ArmCertMemPipe.TailELdpPost
import ArmCertMemPipe.TailEStrU32
import ArmCertMemPipe.TailEStrU64Sp
import ArmCertMemPipe.TailEStrbU
import ArmCertMemPipe.TailEStpPre
import DefaultMemTail
import ActionControls
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultLdrU32
open ArmCertMemPipe ArmCertMemPipe.LdrU32 ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec config rows mapping m imm12 Rn) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [(.x (RegBind.rk Rt), .drop)] (fun f g => Pay mapping imm12 Rn Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.LdrU32.addr f Rn imm12) false 4) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨pa, mapped, mmio, outside, halign, ⟨data, bytes⟩, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.LdrU32.query fetched Rn imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.LdrU32.query fetched Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.LdrU32.query fetched Rn imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.LdrU32.addr (actionState sel sp K) Rn imm12 = MemClass.LdrU32.addr fetched Rn imm12 := by
    simp only [MemClass.LdrU32.addr, ActionTransport.gpr e20]
  have qEq : ∀ acc, MemClass.LdrU32.query (actionState sel sp K) Rn imm12 acc = MemClass.LdrU32.query fetched Rn imm12 acc := by
    intro acc; simp only [MemClass.LdrU32.query, aEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultRuntimeReadFour.runD spec config rows mapping (actionState sel sp K) imm12 Rn Rt hRn hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [aEq]; exact halign) pa (by rw [aEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t Rt data hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (fetched.regs.gpr).set (GPRSummary.key Rt.toNat).val (MemClass.LdrU32.val data)
      (GPRSummary.key Rt.toNat).isLt := by
    rw [hr]; unfold MemClass.LdrU32.post CryptoMem.MemCore.setGpr; dsimp only; rw [ActionTransport.gpr e20]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · exact ArmCertR14.Value.holds_drop1 fetched fin _ (MemClass.LdrU32.val data) (by rw [output.gpr, hgT]; rfl)
      (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT]; rfl, by rw [output.sp, spT]; exact ActionTransport.sp0 e20,
        finMem, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultLdrU32

namespace ReleaseProfile.DefaultLdrU64
open ArmCertMemPipe ArmCertMemPipe.LdrU64 ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL LdrU64.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec config rows mapping m imm12 Rn) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [(.x (RegBind.rk Rt), .drop)] (fun f g => Pay mapping imm12 Rn Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.LdrU64.addr f Rn imm12) false 8) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨pa, mapped, mmio, outside, halign, ⟨data, bytes⟩, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.LdrU64.query fetched Rn imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.LdrU64.query fetched Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.LdrU64.query fetched Rn imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.LdrU64.addr (actionState sel sp K) Rn imm12 = MemClass.LdrU64.addr fetched Rn imm12 := by
    simp only [MemClass.LdrU64.addr, ActionTransport.gpr e20]
  have qEq : ∀ acc, MemClass.LdrU64.query (actionState sel sp K) Rn imm12 acc = MemClass.LdrU64.query fetched Rn imm12 acc := by
    intro acc; simp only [MemClass.LdrU64.query, aEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultLdrU64.runD spec config rows mapping (actionState sel sp K) imm12 Rn Rt hRn hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [aEq]; exact halign) pa (by rw [aEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t Rt data hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 3#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 3#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 3#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (fetched.regs.gpr).set (GPRSummary.key Rt.toNat).val (MemClass.LdrU64.val data)
      (GPRSummary.key Rt.toNat).isLt := by
    rw [hr]; unfold MemClass.LdrU64.post CryptoMem.MemCore.setGpr; dsimp only; rw [ActionTransport.gpr e20]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · exact ArmCertR14.Value.holds_drop1 fetched fin _ (MemClass.LdrU64.val data) (by rw [output.gpr, hgT]; rfl)
      (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT]; rfl, by rw [output.sp, spT]; exact ActionTransport.sp0 e20,
        finMem, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultLdrU64

namespace ReleaseProfile.DefaultLdrU64Sp
open ArmCertMemPipe ArmCertMemPipe.LdrU64Sp ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL LdrU64Sp.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rt : BitVec 5) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec config rows mapping m imm12) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [(.x (RegBind.rk Rt), .drop)] (fun f g => Pay mapping imm12 Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.LdrU64Sp.addr f imm12) false 8) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, pa, mapped, mmio, outside, halign, ⟨data, bytes⟩, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.LdrU64Sp.query fetched imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.LdrU64Sp.query fetched imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.LdrU64Sp.query fetched imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.LdrU64Sp.addr (actionState sel sp K) imm12 = MemClass.LdrU64Sp.addr fetched imm12 := by
    simp only [MemClass.LdrU64Sp.addr, ActionTransport.sp0 e20]
  have qEq : ∀ acc, MemClass.LdrU64Sp.query (actionState sel sp K) imm12 acc = MemClass.LdrU64Sp.query fetched imm12 acc := by
    intro acc; simp only [MemClass.LdrU64Sp.query, aEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultLdrU64Sp.runD spec config rows mapping (actionState sel sp K) imm12 Rt hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [ActionTransport.sp0 e20]; exact hspf) (by rw [aEq]; exact halign) pa (by rw [aEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t Rt data hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (fetched.regs.gpr).set (GPRSummary.key Rt.toNat).val (MemClass.LdrU64Sp.val data)
      (GPRSummary.key Rt.toNat).isLt := by
    rw [hr]; unfold MemClass.LdrU64Sp.post CryptoMem.MemCore.setGpr; dsimp only; rw [ActionTransport.gpr e20]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · exact ArmCertR14.Value.holds_drop1 fetched fin _ (MemClass.LdrU64Sp.val data) (by rw [output.gpr, hgT]; rfl)
      (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT]; rfl, by rw [output.sp, spT]; exact ActionTransport.sp0 e20,
        finMem, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultLdrU64Sp

namespace ReleaseProfile.DefaultLdrbU
open ArmCertMemPipe ArmCertMemPipe.LdrbU ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL LdrbU.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec config rows mapping m imm12 Rn) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [(.x (RegBind.rk Rt), .drop)] (fun f g => Pay mapping imm12 Rn Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.LdrbU.addr f Rn imm12) false 1) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨pa, mapped, mmio, outside, ⟨data, bytes⟩, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.LdrbU.query fetched Rn imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.LdrbU.query fetched Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.LdrbU.query fetched Rn imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.LdrbU.addr (actionState sel sp K) Rn imm12 = MemClass.LdrbU.addr fetched Rn imm12 := by
    simp only [MemClass.LdrbU.addr, ActionTransport.gpr e20]
  have qEq : ∀ acc, MemClass.LdrbU.query (actionState sel sp K) Rn imm12 acc = MemClass.LdrbU.query fetched Rn imm12 acc := by
    intro acc; simp only [MemClass.LdrbU.query, aEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultLdrbU.runD spec config rows mapping (actionState sel sp K) imm12 Rn Rt hRn hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      pa (by rw [aEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t Rt data hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (fetched.regs.gpr).set (GPRSummary.key Rt.toNat).val (MemClass.LdrbU.val data)
      (GPRSummary.key Rt.toNat).isLt := by
    rw [hr]; unfold MemClass.LdrbU.post CryptoMem.MemCore.setGpr; dsimp only; rw [ActionTransport.gpr e20]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · exact ArmCertR14.Value.holds_drop1 fetched fin _ (MemClass.LdrbU.val data) (by rw [output.gpr, hgT]; rfl)
      (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT]; rfl, by rw [output.sp, spT]; exact ActionTransport.sp0 e20,
        finMem, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultLdrbU

namespace ReleaseProfile.DefaultLdpPost
open ArmCertMemPipe ArmCertMemPipe.LdpPost ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL LdpPost.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m) catalogue) D sel {} K
      source (source.regs._PC + 4#64)
      [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)] (fun f g => Pay mapping Rt Rt2 imm7 f g ∧ EvD spec (DataRecs.dataRecs spec (f.regs.SP_EL0) false 16) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, pa, mapped, mmio, ⟨data, bytes⟩, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.LdpPost.query fetched imm7 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.LdpPost.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.LdpPost.query fetched imm7 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have qEq : ∀ acc, MemClass.LdpPost.query (actionState sel sp K) imm7 acc = MemClass.LdpPost.query fetched imm7 acc := by
    intro acc; simp only [MemClass.LdpPost.query, MemClass.LdpPost.ldpAddr, spEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he⟩ := ReleaseProfile.DefaultLdpPost.runD spec config rows mapping (actionState sel sp K) imm7 Rt Rt2 hRt hRt2 hRtt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (feat ▸ ctx.feat.2.2.2) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [spEq]; exact hspf) (by simp only [MemClass.LdpPost.ldpAddr, spEq]; exact hspf)
      pa (by simp only [MemClass.LdpPost.ldpAddr, spEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
  obtain ⟨dataAddress, dataMiddle, dataTraffic, dataEvent, draws, decodeDelta, drawBound⟩ := he
  have he : ∃ ad mid, NoUpdateTraffic spec (MemClass.LdpPost.ldpAddr (actionState sel sp K) imm7) (actionState sel sp K).events ad mid ∧
        t.events = mid.push (.memRead pa.toNat 16 (some (MemClass.LdpPost.ldpAddr (actionState sel sp K) imm7).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) := ⟨dataAddress, dataMiddle, dataTraffic, dataEvent⟩
  obtain ⟨af, npe, gic0, ph⟩ := frames _ t Rt Rt2 imm7 data hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (MemClass.LdpPost.ldpPost fetched Rt Rt2 imm7 data).regs.gpr := by
    rw [hr]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, CryptoMem.MemCore.setGpr, ActionTransport.gpr e20]
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3) := by
    rw [hr]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, spEq]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  rw [actEvents] at he
  obtain ⟨d, hd, _⟩ := HeapV2StepCerts.MemTail.single_delta he (HeapV2StepCerts.MemTail.memRead_covered _ _ _ _)
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · refine ArmCertR14.Value.holds_pair_sp fetched fin _ _ c (MemClass.LdpPost.ldpLo data) (MemClass.LdpPost.ldpHi data)
      (by rw [output.gpr, hgT]; rfl) (by rw [output.sp, hspT, hc])
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT], by rw [output.sp, hspT], finMem, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨d, by rw [events, hd],
      fun nd => by rw [DataRecs.single_records he hd nd]; simp only [MemClass.LdpPost.ldpAddr, spEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultLdpPost

namespace ReleaseProfile.DefaultLdpOff
open ArmCertMemPipe ArmCertMemPipe.LdpOff ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL LdpOff.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m imm7) catalogue) D sel {} K
      source (source.regs._PC + 4#64)
      [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop)] (fun f g => Pay mapping Rt Rt2 imm7 f g ∧ EvD spec (DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr f imm7) false 16) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, half, pa, mapped, mmio, ⟨data, bytes⟩, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.Ldp.query fetched imm7 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.Ldp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldp.query fetched imm7 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have qEq : ∀ acc, MemClass.Ldp.query (actionState sel sp K) imm7 acc = MemClass.Ldp.query fetched imm7 acc := by
    intro acc; simp only [MemClass.Ldp.query, ArmCertMem.LdpEval.ldpAddr, spEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he⟩ := ReleaseProfile.DefaultLdpOffset.runMTE2 spec config rows mapping (actionState sel sp K) imm7 Rt Rt2 hRt hRt2 hRtt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (feat ▸ ctx.feat.2.2.2) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [spEq]; exact hspf) (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact half)
      pa (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
  obtain ⟨dataAddress, dataMiddle, dataTraffic, dataEvent, draws, decodeDelta, drawBound⟩ := he
  have he : ∃ ad mid, NoUpdateTraffic spec (ArmCertMem.LdpEval.ldpAddr (actionState sel sp K) imm7) (actionState sel sp K).events ad mid ∧
        t.events = mid.push (.memRead pa.toNat 16 (some (ArmCertMem.LdpEval.ldpAddr (actionState sel sp K) imm7).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) := ⟨dataAddress, dataMiddle, dataTraffic, dataEvent⟩
  obtain ⟨af, npe, gic0, ph⟩ := frames _ t Rt Rt2 data hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (ArmCertMem.LdpEval.ldpPost fetched Rt Rt2 data).regs.gpr := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, ActionTransport.gpr e20]
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, spEq]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  rw [actEvents] at he
  obtain ⟨d, hd, _⟩ := HeapV2StepCerts.MemTail.single_delta he (HeapV2StepCerts.MemTail.memRead_covered _ _ _ _)
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · refine holds_pair fetched fin _ _ (ArmCertMem.LdpEval.ldpLo data) (ArmCertMem.LdpEval.ldpHi data)
      (by rw [output.gpr, hgT]; rfl) (by rw [output.sp, hspT])
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT], by rw [output.sp, hspT], finMem, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨d, by rw [events, hd],
      fun nd => by rw [DataRecs.single_records he hd nd]; simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultLdpOff

namespace ReleaseProfile.DefaultStrU32
open ArmCertMemPipe ArmCertMemPipe.StrU32 ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL StrU32.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m D imm12 Rn) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [] (fun f g => Pay mapping imm12 Rn Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.StrU32.addr f Rn imm12) true 4) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨pa, mapped, mmio, halign, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.StrU32.query fetched Rn imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.StrU32.query fetched Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.StrU32.query fetched Rn imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.StrU32.addr (actionState sel sp K) Rn imm12 = MemClass.StrU32.addr fetched Rn imm12 := by
    simp only [MemClass.StrU32.addr, ActionTransport.gpr e20]
  have qEq : ∀ acc, MemClass.StrU32.query (actionState sel sp K) Rn imm12 acc = MemClass.StrU32.query fetched Rn imm12 acc := by
    intro acc; simp only [MemClass.StrU32.query, aEq]
  have dEq : MemClass.StrU32.stData (actionState sel sp K) Rt = MemClass.StrU32.stData fetched Rt := by
    simp only [MemClass.StrU32.stData, ActionTransport.gpr e20]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultStrU32.runD spec config rows mapping (actionState sel sp K) imm12 Rn Rt hRn hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [aEq]; exact halign) pa (by rw [aEq]; exact mapped) mmio
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd true acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = MemM1.MemWriteD1.wfold fetched.mem pa.toNat 4
      (fun j => (Sail.BitVec.castWidth (m := 8 * 4) (MemClass.StrU32.stData fetched Rt)).extractLsb' (8 * j) 8) := by
    rw [output.mem, hm, actMem, dEq]
  have gprT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact ActionTransport.gpr e20
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 4, hook, nativePrefix.trans tail, frame, finalQuiet,
    finalPins, sys, ?_, ?_, ?_, gic, ?_, nonProj, ?_, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · intro x hx
    show fin.mem[x]? = fetched.mem[x]?
    rw [finMem, MemM1.MemWriteD1.wfold_get, if_neg hx]
  · intro a ha hw
    exact outside (a - pa.toNat) (by omega) (by rw [show pa.toNat + (a - pa.toNat) = a by omega]; exact ha)
  · intro x hw
    have := inD (x - pa.toNat) (by omega)
    rwa [show pa.toNat + (x - pa.toNat) = x by omega] at this
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · intro a h; rw [finMem]; exact MemTail.wfold_isSome _ _ _ _ _ h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr, gprT]) (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, mapped, finMem, by rw [output.gpr, gprT], by rw [output.sp, spT]; exact ActionTransport.sp0 e20, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultStrU32

namespace ReleaseProfile.DefaultStrU64Sp
open ArmCertMemPipe ArmCertMemPipe.StrU64Sp ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL StrU64Sp.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rt : BitVec 5) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 0#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m D imm12) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [] (fun f g => Pay mapping imm12 Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.StrU64Sp.addr f imm12) true 8) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, pa, mapped, mmio, halign, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.StrU64Sp.query fetched imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.StrU64Sp.query fetched imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.StrU64Sp.query fetched imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.StrU64Sp.addr (actionState sel sp K) imm12 = MemClass.StrU64Sp.addr fetched imm12 := by
    simp only [MemClass.StrU64Sp.addr, ActionTransport.sp0 e20]
  have qEq : ∀ acc, MemClass.StrU64Sp.query (actionState sel sp K) imm12 acc = MemClass.StrU64Sp.query fetched imm12 acc := by
    intro acc; simp only [MemClass.StrU64Sp.query, aEq]
  have dEq : MemClass.StrU64Sp.stData (actionState sel sp K) Rt = MemClass.StrU64Sp.stData fetched Rt := by
    simp only [MemClass.StrU64Sp.stData, ActionTransport.gpr e20]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultStrU64Sp.runD spec config rows mapping (actionState sel sp K) imm12 Rt hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [ActionTransport.sp0 e20]; exact hspf) (by rw [aEq]; exact halign) pa (by rw [aEq]; exact mapped) mmio
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd true acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 0#2 3#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 0#2 3#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 0#2 3#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = MemM1.MemWriteD1.wfold fetched.mem pa.toNat 8
      (fun j => (Sail.BitVec.castWidth (m := 8 * 8) (MemClass.StrU64Sp.stData fetched Rt)).extractLsb' (8 * j) 8) := by
    rw [output.mem, hm, actMem, dEq]
  have gprT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact ActionTransport.gpr e20
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 8, hook, nativePrefix.trans tail, frame, finalQuiet,
    finalPins, sys, ?_, ?_, ?_, gic, ?_, nonProj, ?_, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · intro x hx
    show fin.mem[x]? = fetched.mem[x]?
    rw [finMem, MemM1.MemWriteD1.wfold_get, if_neg hx]
  · intro a ha hw
    exact outside (a - pa.toNat) (by omega) (by rw [show pa.toNat + (a - pa.toNat) = a by omega]; exact ha)
  · intro x hw
    have := inD (x - pa.toNat) (by omega)
    rwa [show pa.toNat + (x - pa.toNat) = x by omega] at this
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · intro a h; rw [finMem]; exact MemTail.wfold_isSome _ _ _ _ _ h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr, gprT]) (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, mapped, finMem, by rw [output.gpr, gprT], by rw [output.sp, spT]; exact ActionTransport.sp0 e20, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultStrU64Sp

namespace ReleaseProfile.DefaultStrbU
open ArmCertMemPipe ArmCertMemPipe.StrbU ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL StrbU.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m D imm12 Rn) catalogue) D sel {} K
      source (source.regs._PC + 4#64) [] (fun f g => Pay mapping imm12 Rn Rt f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.StrbU.addr f Rn imm12) true 1) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨pa, mapped, mmio, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.StrbU.query fetched Rn imm12 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.StrbU.query fetched Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.StrbU.query fetched Rn imm12 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have aEq : MemClass.StrbU.addr (actionState sel sp K) Rn imm12 = MemClass.StrbU.addr fetched Rn imm12 := by
    simp only [MemClass.StrbU.addr, ActionTransport.gpr e20]
  have qEq : ∀ acc, MemClass.StrbU.query (actionState sel sp K) Rn imm12 acc = MemClass.StrbU.query fetched Rn imm12 acc := by
    intro acc; simp only [MemClass.StrbU.query, aEq]
  have dEq : MemClass.StrbU.stData (actionState sel sp K) Rt = MemClass.StrbU.stData fetched Rt := by
    simp only [MemClass.StrbU.stData, ActionTransport.gpr e20]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he, draws, decodeDelta, drawBound⟩ := ReleaseProfile.DefaultStrbU.runD spec config rows mapping (actionState sel sp K) imm12 Rn Rt hRn hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (ActionTransport.dcache e20 ctx.dcache)
      pa (by rw [aEq]; exact mapped) mmio
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd true acc sh)
  obtain ⟨af, npe, gic0, ph, spT⟩ := frames _ t hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) enc0 sp
    currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = MemM1.MemWriteD1.wfold fetched.mem pa.toNat 1
      (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (MemClass.StrbU.stData fetched Rt)).extractLsb' (8 * j) 8) := by
    rw [output.mem, hm, actMem, dEq]
  have gprT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact ActionTransport.gpr e20
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, flags, leafF, slots, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, _⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 1, hook, nativePrefix.trans tail, frame, finalQuiet,
    finalPins, sys, ?_, ?_, ?_, gic, ?_, nonProj, ?_, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · intro x hx
    show fin.mem[x]? = fetched.mem[x]?
    rw [finMem, MemM1.MemWriteD1.wfold_get, if_neg hx]
  · intro a ha hw
    exact outside (a - pa.toNat) (by omega) (by rw [show pa.toNat + (a - pa.toNat) = a by omega]; exact ha)
  · intro x hw
    have := inD (x - pa.toNat) (by omega)
    rwa [show pa.toNat + (x - pa.toNat) = x by omega] at this
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · intro a h; rw [finMem]; exact MemTail.wfold_isSome _ _ _ _ _ h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr, gprT]) (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, mapped, finMem, by rw [output.gpr, gprT], by rw [output.sp, spT]; exact ActionTransport.sp0 e20, ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨_, by rw [events, after, Array.push_eq_append, hd, Array.append_assoc],
      fun nd => by rw [DataRecs.single_records ⟨address, _, ⟨info, walk, leaf, middle, traffic, flags, leafF, slots, rfl⟩, after⟩
        (by rw [after, Array.push_eq_append, hd, Array.append_assoc]) nd, aEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultStrbU

namespace ReleaseProfile.DefaultStpPre
open ArmCertMemPipe ArmCertMemPipe.StpPre ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL StpPre.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) 
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m D imm7) catalogue) D sel {} K
      source (source.regs._PC + 4#64)
      [(.sp, .set .sp c)] (fun f g => Pay mapping Rt Rt2 imm7 f g ∧ EvD spec (DataRecs.dataRecs spec (MemClass.StpPre.ldpAddr f imm7) true 16) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, half, pa, mapped, mmio, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.StpPre.query fetched imm7 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.StpPre.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.StpPre.query fetched imm7 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have qEq : ∀ acc, MemClass.StpPre.query (actionState sel sp K) imm7 acc = MemClass.StpPre.query fetched imm7 acc := by
    intro acc; simp only [MemClass.StpPre.query, MemClass.StpPre.ldpAddr, spEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he⟩ := ReleaseProfile.DefaultStpPre.runD spec config rows mapping (actionState sel sp K) imm7 Rt Rt2 hRt hRt2
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (feat ▸ ctx.feat.2.2.2) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [spEq]; exact hspf) (by simp only [MemClass.StpPre.ldpAddr, spEq]; exact half)
      pa (by simp only [MemClass.StpPre.ldpAddr, spEq]; exact mapped) mmio
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd true acc sh)
  obtain ⟨dataAddress, dataMiddle, dataTraffic, dataEvent, draws, decodeDelta, drawBound⟩ := he
  have he : ∃ ad mid, NoUpdateTraffic spec (MemClass.StpPre.ldpAddr (actionState sel sp K) imm7) (actionState sel sp K).events ad mid ∧
        t.events = mid.push (.memWrite pa.toNat 16 (some (MemClass.StpPre.ldpAddr (actionState sel sp K) imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (MemClass.StpPre.stpData (actionState sel sp K) Rt Rt2))) none) := ⟨dataAddress, dataMiddle, dataTraffic, dataEvent⟩
  obtain ⟨af, npe, gic0, ph⟩ := frames _ t imm7 hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have dEq : MemClass.StpPre.stpData (actionState sel sp K) Rt Rt2 = MemClass.StpPre.stpData fetched Rt Rt2 := by
    simp only [MemClass.StpPre.stpData, ActionTransport.gpr e20]
  have finMem : fin.mem = MemM1.MemWriteD1.wfold fetched.mem pa.toNat 16
      (MemM1.MemWriteD4.wbyte (MemClass.StpPre.stpData fetched Rt Rt2)) := by
    rw [output.mem, hm, actMem, dEq]
  have hgT : t.regs.gpr = fetched.regs.gpr := by
    rw [hr]; show (actionState sel sp K).regs.gpr = _; exact ActionTransport.gpr e20
  have hspT : t.regs.SP_EL0 = MemClass.StpPre.ldpAddr fetched imm7 := by
    rw [hr]; simp only [MemClass.StpPre.ldpAddr, spEq]
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  rw [actEvents] at he
  obtain ⟨d, hd, _⟩ := HeapV2StepCerts.MemTail.single_delta he (HeapV2StepCerts.MemTail.memWrite_covered _ _ _ _ _ _)
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16, hook, nativePrefix.trans tail, frame, finalQuiet,
    finalPins, sys, ?_, ?_, ?_, gic, ?_, nonProj, ?_, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · intro x hx
    show fin.mem[x]? = fetched.mem[x]?
    rw [finMem, MemM1.MemWriteD1.wfold_get, if_neg hx]
  · intro a ha hw
    exact outside (a - pa.toNat) (by omega) (by rw [show pa.toNat + (a - pa.toNat) = a by omega]; exact ha)
  · intro x hw
    have := inD (x - pa.toNat) (by omega)
    rwa [show pa.toNat + (x - pa.toNat) = x by omega] at this
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · intro a h; rw [finMem]; exact MemTail.wfold_isSome _ _ _ _ _ h
  · refine ArmCertR14.Value.holds_sp fetched fin c (by rw [output.gpr, hgT]) ?_
    rw [output.sp, hspT, ← hc]
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, mapped, finMem, by rw [output.gpr, hgT], by rw [output.sp, hspT], ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨d, by rw [events, hd],
      fun nd => by rw [DataRecs.single_records he hd nd]; simp only [MemClass.StpPre.ldpAddr, spEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultStpPre

namespace ReleaseProfile.DefaultStpOff
open ArmCertMemPipe ArmCertMemPipe.StpOff ReleaseProfile.DefaultMemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

#check "CURRENT_DECL StpOff.tailGE"
theorem tailGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) 
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue) (source : NativeState) :
    MemTailAt real spec config rows (GCtxDefault spec config rows mapping m (Facts spec mapping m D imm7) catalogue) D sel {} K
      source (source.regs._PC + 4#64)
      [] (fun f g => Pay mapping Rt Rt2 imm7 f g ∧ EvD spec (DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr f imm7) true 16) f g) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, half, pa, mapped, mmio, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.Stp.query fetched imm7 acc) ∧
      ∃ d : S1AccessData spec config rows (MemClass.Stp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query fetched imm7 acc) d fetched := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, d, cur⟩
  obtain ⟨sp, hook, postS, hookDelta⟩ :=
    NativeTagCheck.Hooks.pmu_event_choice (budget + 1) fetched quiet PMU_EVENT_INST_SPEC
  have metadataDelta : NativeMteTagCheck.ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans hookDelta
      (NativeTagCheck.metadata_choice sel sp K)
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have qEq : ∀ acc, MemClass.Stp.query (actionState sel sp K) imm7 acc = MemClass.Stp.query fetched imm7 acc := by
    intro acc; simp only [MemClass.Stp.query, ArmCertMem.LdpEval.ldpAddr, spEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he⟩ := ReleaseProfile.DefaultStpOffset.runMTE2 spec config rows mapping (actionState sel sp K) imm7 Rt Rt2 hRt hRt2
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ReleaseProfile.ActionControls.post e20 ctx.post)
      catalogue (DefaultActionControls.default_at e20 ctx.controls)
      (NativeMteTagCheck.tag_status_transport metadataDelta ctx.allowed)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (feat ▸ ctx.feat.2.2.2) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [spEq]; exact hspf) (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact half)
      pa (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact mapped) mmio
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd true acc sh)
  obtain ⟨dataAddress, dataMiddle, dataTraffic, dataEvent, draws, decodeDelta, drawBound⟩ := he
  have he : ∃ ad mid, NoUpdateTraffic spec (ArmCertMem.LdpEval.ldpAddr (actionState sel sp K) imm7) (actionState sel sp K).events ad mid ∧
        t.events = mid.push (.memWrite pa.toNat 16 (some (ArmCertMem.LdpEval.ldpAddr (actionState sel sp K) imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (ArmCertMem.StpEval.stpData (actionState sel sp K) Rt Rt2))) none) := ⟨dataAddress, dataMiddle, dataTraffic, dataEvent⟩
  obtain ⟨af, npe, gic0, ph⟩ := frames _ t hr
  have fields : GuardFieldsEq (actionState sel sp K) t := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  have frame : NativeEntryContract.Frame {} (actionState sel sp K) t := NativeEntryContract.of_scalar af npe gic0
  have tq : HookQuiet (budget + 1) t := quiet_of_fields (budget + 1) _ t metadataQuiet fields
  have boundary := metadata_boundary_at real source sel
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have afterDelta := NativeTagCheck.after_action_choice_of_run real source sel enc0 t fin budget
    tq actionPins enc eret actionIT actionSS tail
  have totalDelta : NativeMteTagCheck.ChoiceDelta fetched fin draws := by
    simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
      (NativeMteTagCheck.choice_delta_trans metadataDelta decodeDelta) afterDelta
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have dEq : ArmCertMem.StpEval.stpData (actionState sel sp K) Rt Rt2 = ArmCertMem.StpEval.stpData fetched Rt Rt2 := by
    simp only [ArmCertMem.StpEval.stpData, ActionTransport.gpr e20]
  have finMem : fin.mem = MemM1.MemWriteD1.wfold fetched.mem pa.toNat 16
      (MemM1.MemWriteD4.wbyte (ArmCertMem.StpEval.stpData fetched Rt Rt2)) := by
    rw [output.mem, hm, actMem, dEq]
  have hgT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact ActionTransport.gpr e20
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by rw [hr]; exact spEq
  have actEvents : (actionState sel sp K).events = fetched.events :=
    (actionState_events sel sp K).trans postS.events
  rw [actEvents] at he
  obtain ⟨d, hd, _⟩ := HeapV2StepCerts.MemTail.single_delta he (HeapV2StepCerts.MemTail.memWrite_covered _ _ _ _ _ _)
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16, hook, nativePrefix.trans tail, frame, finalQuiet,
    finalPins, sys, ?_, ?_, ?_, gic, ?_, nonProj, ?_, ?_, ?_, ⟨draws, totalDelta, drawBound⟩⟩
  · intro x hx
    show fin.mem[x]? = fetched.mem[x]?
    rw [finMem, MemM1.MemWriteD1.wfold_get, if_neg hx]
  · intro a ha hw
    exact outside (a - pa.toNat) (by omega) (by rw [show pa.toNat + (a - pa.toNat) = a by omega]; exact ha)
  · intro x hw
    have := inD (x - pa.toNat) (by omega)
    rwa [show pa.toNat + (x - pa.toNat) = x by omega] at this
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · intro a h; rw [finMem]; exact MemTail.wfold_isSome _ _ _ _ _ h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr, hgT]) (by rw [output.sp, hspT])
  · refine ⟨?_, ?_⟩
    · refine ⟨pa, mapped, finMem, by rw [output.gpr, hgT], by rw [output.sp, hspT], ?_⟩
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h
    · exact ⟨d, by rw [events, hd],
      fun nd => by rw [DataRecs.single_records he hd nd]; simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; rfl⟩

#print axioms tailGE
end ReleaseProfile.DefaultStpOff
