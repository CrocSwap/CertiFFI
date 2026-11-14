-- Memory (d200 memory routes): the runtime14 STP (64-bit pair, PRE-INDEX, base SP) memory tail over the program-generic
-- fetched context: SP := SP + off, one LSE2 16-byte store of X[Rt] ++ X[Rt2] at the new SP (DispatchAt hypothesis).
import ArmCertMemPipe.RunD14
import ArmCertMemPipe.EntryMemG
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.C3Byte
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertMemPipe.StpPre
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

/-- Frames of a state whose registers are a.regs with SP := SP + off (no SP conjunct). -/
theorem frames (a u : NativeState) (imm7 : BitVec 7)
    (hr : u.regs = { a.regs with SP_EL0 := MemClass.StpPre.ldpAddr a imm7 }) :
    ActFrame a u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs u.regs ∧
    u.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
    u.regs.PhysicalCount = a.regs.PhysicalCount := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> (rw [hr]; try rfl)
  · unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · rw [hr]; try rfl
  · rw [hr]; try rfl

def Facts {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (D : Nat → Prop) (imm7 : BitVec 7) (f : NativeState) : Prop :=
  f.regs.SP_EL0.toNat % 16 = 0 ∧ (MemClass.StpPre.ldpAddr f imm7).toNat % 16 = 0 ∧
    ∃ pa : BitVec 56, mapping (MemClass.StpPre.ldpAddr f imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    (∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i)) ∧ (∀ i < 16, D (pa.toNat + i)) ∧
    (∀ acc, ArmCert.Translate.Model.DataShape true acc → m.permitted (MemClass.StpPre.ldpAddr f imm7) acc true ((16 : Nat) : Int))

/-- The payload: memory = X[Rt] ++ X[Rt2] written at PA(SP + off); GPRs unchanged; SP := SP + off; NZCV unchanged. -/
def Pay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (f g : NativeState) : Prop :=
  ∃ pa : BitVec 56, mapping (MemClass.StpPre.ldpAddr f imm7) = some pa.toNat ∧
    g.mem = MemM1.MemWriteD1.wfold f.mem pa.toNat 16 (MemM1.MemWriteD4.wbyte (MemClass.StpPre.stpData f Rt Rt2)) ∧
    g.regs.gpr = f.regs.gpr ∧ g.regs.SP_EL0 = MemClass.StpPre.ldpAddr f imm7 ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem tailG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) 
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) :
    MemTailGAt real spec config rows (GCtx spec config rows mapping m (Facts spec mapping m D imm7)) D sel {} K
      source (source.regs._PC + 4#64)
      [(.sp, .set .sp c)] (Pay mapping Rt Rt2 imm7) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨hspf, half, pa, mapped, mmio, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.StpPre.query fetched imm7 acc) ∧
      (∃ d : S1AccessData spec config rows (MemClass.StpPre.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.StpPre.query fetched imm7 acc) d fetched) ∧
      MemM1.MemWriteD6.PreW acc fetched.regs := by
    intro acc sh
    obtain ⟨⟨va', ⟨raw', al'⟩, size'⟩, hva', hraw, hal, hsize, inDomain, d, cur⟩ := ctx.closed _ acc true _ (perm acc sh)
    simp only at hva' hraw hal hsize
    subst hva' hraw hal hsize
    exact ⟨inDomain, ⟨d, cur⟩, C3.preW_of_post2 ctx.post2 _⟩
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
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
  obtain ⟨t, ok, hr, hm, _⟩ := MemClass.StpPre.runD spec config rows mapping (actionState sel sp K) imm7 Rt Rt2 hRt hRt2
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, ⟨d, access⟩, pre⟩ := perAcc acc sh
        exact ⟨member, ⟨d, ActionTransport.access e20 access⟩, ActionTransport.preW e20 pre⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ActionTransport.post2 e20 ctx.post2)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (feat ▸ ctx.feat.2.2.2) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [spEq]; exact hspf) (by simp only [MemClass.StpPre.ldpAddr, spEq]; exact half)
      pa (by simp only [MemClass.StpPre.ldpAddr, spEq]; exact mapped) mmio
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd true acc sh)
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
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, _, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
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
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16, hook, nativePrefix.trans tail, frame, finalQuiet,
    finalPins, sys, ?_, ?_, ?_, gic, ?_, nonProj, ?_, ?_, ?_⟩
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
  · refine ⟨pa, mapped, finMem, by rw [output.gpr, hgT], by rw [output.sp, hspT], ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms tailG
end ArmCertMemPipe.StpPre
