-- Memory (d200 memory routes, shape): the runtime14 LDR (unsigned, 64-bit, Rn < 31) memory tail over the
-- program-generic fetched context, as HeapV2StepCerts.MemTail.mem_tailD_Ldrb with the dispatch / word / metadata index
-- abstracted (DispatchAt hypothesis: emits it) and the access facts taken from the GCtx program part (Facts).
import ArmCertMemPipe.RunD14
import ArmCertMemPipe.EntryMemG
import HeapV2StepCerts.MemTailD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertMemPipe.LdrU64Sp
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)

/-- Canonical frames of a state whose registers are MemClass.LdrU64Sp.post a Rt d (old-bridge vocabulary, as Ldrb.frames). -/
theorem frames (a u : NativeState) (Rt : BitVec 5) (d : BitVec (8 * 8))
    (hr : u.regs = (MemClass.LdrU64Sp.post a Rt d).regs) :
    ActFrame a u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs u.regs ∧
    u.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
    u.regs.PhysicalCount = a.regs.PhysicalCount ∧ u.regs.SP_EL0 = a.regs.SP_EL0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> (rw [hr]; try rfl)
  · unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · rw [hr]; try rfl
  · rw [hr]; rfl
  · rw [hr]; rfl

/-- The access facts the tail needs at the fetched state (the route's program part X). -/
def Facts {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm12 : BitVec 12)
    (f : NativeState) : Prop :=
  f.regs.SP_EL0.toNat % 16 = 0 ∧ ∃ pa : BitVec 56, mapping (MemClass.LdrU64Sp.addr f imm12) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    ¬ (rowsFootprint spec.imageRows).byte pa.toNat ∧ (MemClass.LdrU64Sp.addr f imm12).toNat % 8 = 0 ∧
    (∃ data : BitVec (8 * 8), ∀ i < 8, f.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
    (∀ acc, ArmCert.Translate.Model.DataShape false acc →
      m.permitted (MemClass.LdrU64Sp.addr f imm12) acc true ((8 : Nat) : Int))

/-- The class payload: X[Rt] := the 8 bytes at the access PA; SP, memory and NZCV unchanged. -/
def Pay (mapping : BitVec 64 → Option Nat) (imm12 : BitVec 12) (Rt : BitVec 5) (f g : NativeState) : Prop :=
  ∃ (pa : BitVec 56) (data : BitVec (8 * 8)), mapping (MemClass.LdrU64Sp.addr f imm12) = some pa.toNat ∧
    (∀ i < 8, f.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
    g.regs.gpr = (MemClass.LdrU64Sp.post f Rt data).regs.gpr ∧ g.regs.SP_EL0 = f.regs.SP_EL0 ∧
    g.mem = f.mem ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem tailG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rt : BitVec 5) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) :
    MemTailGAt real spec config rows (GCtx spec config rows mapping m (Facts spec config rows mapping m imm12)) D sel {} K
      source (source.regs._PC + 4#64) [(.x (RegBind.rk Rt), .drop)] (Pay mapping imm12 Rt) := by
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
  have aEq : MemClass.LdrU64Sp.addr (actionState sel sp K) imm12 = MemClass.LdrU64Sp.addr fetched imm12 := by
    simp only [MemClass.LdrU64Sp.addr, ActionTransport.sp0 e20]
  have qEq : ∀ acc, MemClass.LdrU64Sp.query (actionState sel sp K) imm12 acc = MemClass.LdrU64Sp.query fetched imm12 acc := by
    intro acc; simp only [MemClass.LdrU64Sp.query, aEq]
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t, ok, hr, hm, he⟩ := MemClass.LdrU64Sp.runD spec config rows mapping (actionState sel sp K) imm12 Rt hRt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        rw [qEq acc]
        obtain ⟨member, d, access⟩ := perAcc acc sh
        exact ⟨member, d, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 ctx.mode) (ActionTransport.debug e20 ctx.debug) (ActionTransport.post2 e20 ctx.post2)
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
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, _, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source sel enc0 t budget tq actionPins next enc eret actionIT actionSS
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (fetched.regs.gpr).set (GPRSummary.key Rt.toNat).val (MemClass.LdrU64Sp.val data)
      (GPRSummary.key Rt.toNat).isLt := by
    rw [hr]; unfold MemClass.LdrU64Sp.post CryptoMem.MemCore.setGpr; dsimp only; rw [ActionTransport.gpr e20]
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · exact ArmCertR14.Value.holds_drop1 fetched fin _ (MemClass.LdrU64Sp.val data) (by rw [output.gpr, hgT]; rfl)
      (by rw [output.sp, spT]; exact ActionTransport.sp0 e20)
  · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT]; rfl, by rw [output.sp, spT]; exact ActionTransport.sp0 e20,
      finMem, ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms tailG
end ArmCertMemPipe.LdrU64Sp
