-- Memory (d200 memory routes): the runtime14 STR (unsigned, 64-bit, Rn < 31) memory tail over the program-generic fetched
-- context, as HeapV2StepCerts.MemTail.mem_tailD_Strb with dispatch / word / metadata index abstracted (DispatchAt
-- hypothesis) and the access facts from the GCtx program part (Facts, with the caller-chosen write set D).
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
namespace ArmCertMemPipe.StrbU
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

/-- Frames of a store whose registers are unchanged (old-bridge vocabulary). -/
theorem frames (a u : NativeState) (hr : u.regs = a.regs) :
    ActFrame a u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs u.regs ∧
    u.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
    u.regs.PhysicalCount = a.regs.PhysicalCount ∧ u.regs.SP_EL0 = a.regs.SP_EL0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> (rw [hr]; try rfl)
  · unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · rw [hr]
  · rw [hr]
  · rw [hr]

/-- The access facts at the fetched state (route program part X); D is the caller's write set. -/
def Facts {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (D : Nat → Prop) (imm12 : BitVec 12) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  ∃ pa : BitVec 56, mapping (MemClass.StrbU.addr f Rn imm12) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    (∀ i < 1, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i)) ∧ (∀ i < 1, D (pa.toNat + i)) ∧
    (∀ acc, ArmCert.Translate.Model.DataShape true acc → m.permitted (MemClass.StrbU.addr f Rn imm12) acc true ((1 : Nat) : Int))

/-- The class payload: memory = X[Rt]'s 8 bytes written at the access PA; GPRs / SP / NZCV unchanged. -/
def Pay (mapping : BitVec 64 → Option Nat) (imm12 : BitVec 12) (Rn Rt : BitVec 5) (f g : NativeState) : Prop :=
  ∃ pa : BitVec 56, mapping (MemClass.StrbU.addr f Rn imm12) = some pa.toNat ∧
    g.mem = MemM1.MemWriteD1.wfold f.mem pa.toNat 1
      (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (MemClass.StrbU.stData f Rt)).extractLsb' (8 * j) 8) ∧
    g.regs.gpr = f.regs.gpr ∧ g.regs.SP_EL0 = f.regs.SP_EL0 ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem tailG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) :
    MemTailGAt real spec config rows (GCtx spec config rows mapping m (Facts spec mapping m D imm12 Rn)) D sel {} K
      source (source.regs._PC + 4#64) [] (Pay mapping imm12 Rn Rt) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨pa, mapped, mmio, outside, inD, perm⟩ := ctx.prog
  have perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.StrbU.query fetched Rn imm12 acc) ∧
      (∃ d : S1AccessData spec config rows (MemClass.StrbU.query fetched Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.StrbU.query fetched Rn imm12 acc) d fetched) ∧
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
  have aEq : MemClass.StrbU.addr (actionState sel sp K) Rn imm12 = MemClass.StrbU.addr fetched Rn imm12 := by
    simp only [MemClass.StrbU.addr, ActionTransport.gpr e20]
  have qEq : ∀ acc, MemClass.StrbU.query (actionState sel sp K) Rn imm12 acc = MemClass.StrbU.query fetched Rn imm12 acc := by
    intro acc; simp only [MemClass.StrbU.query, aEq]
  have dEq : MemClass.StrbU.stData (actionState sel sp K) Rt = MemClass.StrbU.stData fetched Rt := by
    simp only [MemClass.StrbU.stData, ActionTransport.gpr e20]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.StrbU.runD spec config rows mapping (actionState sel sp K) imm12 Rn Rt hRn hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, ⟨d, access⟩, pre⟩ := perAcc acc sh
        exact ⟨member, ⟨d, ActionTransport.access e20 access⟩, ActionTransport.preW e20 pre⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ActionTransport.post2 e20 ctx.post2)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
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
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, _, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = MemM1.MemWriteD1.wfold fetched.mem pa.toNat 1
      (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (MemClass.StrbU.stData fetched Rt)).extractLsb' (8 * j) 8) := by
    rw [output.mem, hm, actMem, dEq]
  have gprT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact ActionTransport.gpr e20
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 1, hook, nativePrefix.trans tail, frame, finalQuiet,
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
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr, gprT]) (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨pa, mapped, finMem, by rw [output.gpr, gprT], by rw [output.sp, spT]; exact ActionTransport.sp0 e20, ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms tailG
end ArmCertMemPipe.StrbU
