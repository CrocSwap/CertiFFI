-- Memory (d200 memory routes): the runtime14 LDP (64-bit pair, POST-INDEX, base SP) memory tail over the program-generic
-- fetched context: one LSE2 16-byte load at SP, X[Rt]/X[Rt2] := lo/hi, then SP := SP + off (DispatchAt hypothesis).
import ArmCertMemPipe.RunD14
import ArmCertMemPipe.EntryMemG
import HeapV2StepCerts.MemTailD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertMemPipe.LdpPost
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

/-- Frames of a state whose registers are MemClass.LdpPost.ldpPost a … (SP changes: no SP conjunct). -/
theorem frames (a u : NativeState) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (d : BitVec 128)
    (hr : u.regs = (MemClass.LdpPost.ldpPost a Rt Rt2 imm7 d).regs) :
    ActFrame a u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs u.regs ∧
    u.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
    u.regs.PhysicalCount = a.regs.PhysicalCount := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> (rw [hr]; try rfl)
  · unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · rw [hr]; try rfl
  · rw [hr]; rfl

def Facts {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (f : NativeState) : Prop :=
  f.regs.SP_EL0.toNat % 16 = 0 ∧ ∃ pa : BitVec 56, mapping f.regs.SP_EL0 = some pa.toNat ∧
    MemM1.MemReadIF.NotMMIO pa ∧
    (∃ data : BitVec 128, ∀ i < 16, f.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8)) ∧
    (∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted f.regs.SP_EL0 acc true ((16 : Nat) : Int))

/-- The payload: X[Rt]/X[Rt2] := lo/hi of the 16 bytes at PA(SP); SP := SP + off; memory and NZCV unchanged. -/
def Pay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (f g : NativeState) : Prop :=
  ∃ (pa : BitVec 56) (data : BitVec 128), mapping f.regs.SP_EL0 = some pa.toNat ∧
    (∀ i < 16, f.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8)) ∧
    g.regs.gpr = (MemClass.LdpPost.ldpPost f Rt Rt2 imm7 data).regs.gpr ∧
    g.regs.SP_EL0 = f.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3) ∧
    g.mem = f.mem ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem tailG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) :
    MemTailGAt real spec config rows (GCtx spec config rows mapping m (Facts spec mapping m)) D sel {} K
      source (source.regs._PC + 4#64)
      [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)] (Pay mapping Rt Rt2 imm7) := by
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
  have qEq : ∀ acc, MemClass.LdpPost.query (actionState sel sp K) imm7 acc = MemClass.LdpPost.query fetched imm7 acc := by
    intro acc; simp only [MemClass.LdpPost.query, MemClass.LdpPost.ldpAddr, spEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, _⟩ := MemClass.LdpPost.runD spec config rows mapping (actionState sel sp K) imm7 Rt Rt2 hRt hRt2 hRtt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ActionTransport.post2 e20 ctx.post2)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1) (feat ▸ ctx.feat.2.2.2) (ActionTransport.dcache e20 ctx.dcache)
      (by rw [spEq]; exact hspf) (by simp only [MemClass.LdpPost.ldpAddr, spEq]; exact hspf)
      pa (by simp only [MemClass.LdpPost.ldpAddr, spEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact ctx.raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact ctx.noUpd false acc sh)
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
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, _, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (MemClass.LdpPost.ldpPost fetched Rt Rt2 imm7 data).regs.gpr := by
    rw [hr]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, CryptoMem.MemCore.setGpr, ActionTransport.gpr e20]
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3) := by
    rw [hr]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, spEq]
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · refine ArmCertR14.Value.holds_pair_sp fetched fin _ _ c (MemClass.LdpPost.ldpLo data) (MemClass.LdpPost.ldpHi data)
      (by rw [output.gpr, hgT]; rfl) (by rw [output.sp, hspT, hc])
  · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT], by rw [output.sp, hspT], finMem, ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms tailG
end ArmCertMemPipe.LdpPost
