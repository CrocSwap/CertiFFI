import PairDefault236.LdpOne
import PairDefault236.LdpSplit
import PairDefault236.LdpBytes
import NativeAccess.PairGeometry
import PairDefault236.ActionFacts
import ArmCertMemPipe.EntryMemG
import HeapV2StepCerts.MemTailD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open NativeAccess
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace PairDefault236.PairTail
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts ArmCertMemPipe
open ArmCert.HookQuiet.V0 (HookQuiet)
open PairDefault236.Trace
open TranslateSpan.DefaultAccessTrace NativeMteTagCheck
open NativeAccess.Trace (Access)
open NativeAccess.LdpBytes
attribute [local implicit_reducible] EStateM Arch.arch_ak

/-- Two GPRs clobbered, SP unchanged. -/
theorem holds_pair (x y : HeapV2StepCerts.RegBind.St) (R R2 : Fin 31) (v v2 : BitVec 64)
    (gpr : y.regs.gpr = (x.regs.gpr.set R.val v R.isLt).set R2.val v2 R2.isLt) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) :
    RegBind.Holds [(.x R, .drop), (.x R2, .drop)] x y := by
  intro r
  cases r with
  | sp => simp [RegBind.updOf, List.find?, RegBind.regVal, sp]
  | x j =>
    by_cases h1 : R = j
    · subst h1; simp [RegBind.updOf, List.find?]
    by_cases h2 : R2 = j
    · subst h2; simp [RegBind.updOf, List.find?, h1]
    have e1 : (RegBind.Reg.x R = RegBind.Reg.x j) = False := by simp [h1]
    have e2 : (RegBind.Reg.x R2 = RegBind.Reg.x j) = False := by simp [h2]
    simp only [RegBind.updOf, List.find?, e1, e2, decide_false]
    simp only [RegBind.regVal, gpr, Vector.getElem_set, Fin.val_inj]
    simp [h1, h2]

/-- Frames of a state whose registers are ArmCertMem.LdpEval.ldpPost a … (no SP conjunct). -/
theorem frames (a u : NativeState) (Rt Rt2 : BitVec 5) (d : BitVec 128)
    (hr : u.regs = (ArmCertMem.LdpEval.ldpPost a Rt Rt2 d).regs) :
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

theorem profile_of_sys {p : AccessProfile} {s t : NativeState}
    (pins : ProfileAt p s) (sys : SysEq2 t.regs s.regs) : ProfileAt p t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [← sys.feat]; exact pins.lse2
  · rw [← sys.feat]; exact pins.lrcpc3
  · refine ⟨sys.el.symm.trans pins.host.el,sys.nrw.symm.trans pins.host.nrw,?_,?_,?_,?_,?_,?_⟩
    · rw [← sys.feat]; exact pins.host.aa64
    · rw [← sys.feat]; exact pins.host.rme
    · rw [← sys.feat]; exact pins.host.vhe
    · rw [← sys.scr]; exact pins.host.ns
    · rw [← sys.hcr]; exact pins.host.e2h
    · rw [← sys.hcr]; exact pins.host.tge
  · rw [← sys.sctlr]; exact pins.alignment_disabled

def ByteFacts (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  (pairAddr f Rn imm7).toNat % 8 ≠ 0 ∧
    (∀ j : Fin 16, domain (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int))) ∧
    ∃ (pa : Fin 16 → BitVec 56) (data : BitVec 128),
      (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
      (∀ j : Fin 16, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 16, f.mem[(pa j).toNat]? = some (data.extractLsb' (8 * j.val) 8)) ∧
      (∀ acc, DataShape false acc → ∀ (j : Fin 16) (aligned : Bool),
        m.permitted (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) acc aligned (1 : Int))

def BytePay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f g : NativeState) : Prop :=
  ∃ (pa : Fin 16 → BitVec 56) (data : BitVec 128),
    (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
    (∀ j : Fin 16, f.mem[(pa j).toNat]? = some (data.extractLsb' (8 * j.val) 8)) ∧
    g.regs.gpr = (ArmCertMem.LdpEval.ldpPost f Rt Rt2 data).regs.gpr ∧
    g.regs.SP_EL0 = f.regs.SP_EL0 ∧ g.mem = f.mem ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

#print axioms profile_of_sys

/-- Conditional native-tail component. Program byte facts concern the one
fetched state; all actual descriptor/query certificate families and all later
state facts are constructed inside the proof. This is not CI admission. -/
theorem ldp_bytes_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) (profile : AccessProfile) (sourcePins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows
      (Ctx spec config rows mapping m catalogue 16 (ByteFacts domain mapping m imm7 Rn)) D sel {} K
      source (source.regs._PC + 4#64)
      [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (BytePay mapping Rt Rt2 imm7 Rn) 16 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨not8,member,pa,data,mapped,mmio,bytes,perm⟩ := ctx.prog
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have actionPrefixDelta : ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (NativeTagCheck.spec_choice_of_run (budget+1) fetched sp quiet hook)
      (NativeTagCheck.metadata_choice sel sp K)
  have actionRows := TranslateSpan.DefaultMTE2.rows_after_delta fetched (actionState sel sp K)
    16 16 0 ctx.statusRows actionPrefixDelta (by omega)
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have gprEq := ActionTransport.gpr (w := sel) (K := K) e20
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  have not8A : (pairAddr (actionState sel sp K) Rn imm7).toNat % 8 ≠ 0 := by
    simpa only [pairAddr,gprEq] using not8
  have not16A : (pairAddr (actionState sel sp K) Rn imm7).toNat % 16 ≠ 0 := by omega
  obtain ⟨t,ok,hr,hm,⟨draws,actionDelta,drawBound⟩,memEnd,calls,actualAcc,actualAligned,chain,endEvents,requests⟩ :=
    LdpBytes.run spec config rows mapping (actionState sel sp K) imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
      profile (profile_of_sys sourcePins metadataInput.sys) (feat ▸ ctx.feat.2.2.2)
      (PairGeometry.pairAligned_false _ not8A) (PairGeometry.join_disabled _ _ not16A)
      m (ctx.current.action sel K e20 postS.mem) actionRows pa
      (by intro acc sh j al; simpa only [pairAddr,gprEq] using perm acc sh j al)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
      (by intro j; simpa only [pairAddr,gprEq] using mapped j) mmio data
      (by intro j; rw [actMem]; exact bytes j)
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
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0
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
  have finalDelta := NativeTagCheck.native_tail_choice_of_delta real source fetched sp t fin sel enc0 K budget draws
    quiet hook actionDelta nativePrefix tq actionPins enc eret actionIT actionSS (nativePrefix.trans tail)
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (ArmCertMem.LdpEval.ldpPost fetched Rt Rt2 data).regs.gpr := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, ActionTransport.gpr e20]
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, spEq]
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_,⟨draws,finalDelta,drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · refine holds_pair fetched fin _ _ (ArmCertMem.LdpEval.ldpLo data) (ArmCertMem.LdpEval.ldpHi data)
      (by rw [output.gpr, hgT]; rfl) (by rw [output.sp, hspT])
  · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT], by rw [output.sp, hspT], finMem, ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms ldp_bytes_tailG

def OneFacts (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  NativeMte2.Read.Within16 (pairAddr f Rn imm7) 16 ∧ ∃ (pa : BitVec 56) (data : BitVec 128),
    mapping (pairAddr f Rn imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    (∀ i < 16, f.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
    (∀ acc, DataShape false acc → m.permitted (pairAddr f Rn imm7) acc
      (PairOne.pairAligned (pairAddr f Rn imm7)) (16 : Int))

def OnePay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f g : NativeState) : Prop :=
  ∃ (pa : BitVec 56) (data : BitVec 128), mapping (pairAddr f Rn imm7) = some pa.toNat ∧
    (∀ i < 16, f.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
    g.regs.gpr = (ArmCertMem.LdpEval.ldpPost f Rt Rt2 data).regs.gpr ∧
    g.regs.SP_EL0 = f.regs.SP_EL0 ∧ g.mem = f.mem ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem ldp_one_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) (profile : AccessProfile) (sourcePins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (Ctx spec config rows mapping m catalogue 1 (OneFacts mapping m imm7 Rn))
      D sel {} K source (source.regs._PC + 4#64)
      [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (OnePay mapping Rt Rt2 imm7 Rn) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨fit,pa,data,mapped,mmio,bytes,perm⟩ := ctx.prog
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have actionPrefixDelta : ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (NativeTagCheck.spec_choice_of_run (budget+1) fetched sp quiet hook)
      (NativeTagCheck.metadata_choice sel sp K)
  have actionRows := TranslateSpan.DefaultMTE2.rows_after_delta fetched (actionState sel sp K)
    1 1 0 ctx.statusRows actionPrefixDelta (by omega)
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have gprEq := ActionTransport.gpr (w := sel) (K := K) e20
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t,ok,hr,hm,⟨draws,actionDelta,drawBound⟩,_⟩ :=
    LdpOne.run spec config rows mapping (actionState sel sp K) imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
      profile (profile_of_sys sourcePins metadataInput.sys) (feat ▸ ctx.feat.2.2.2)
      (Control.natural_of_fit _ (by simpa [pairAddr,gprEq] using fit))
      (by simpa only [pairAddr,gprEq] using fit)
      m (ctx.current.action sel K e20 postS.mem) actionRows
      (by intro acc sh; simpa only [pairAddr,gprEq] using perm acc sh)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
      pa (by simpa only [pairAddr,gprEq] using mapped) mmio data
      (by intro i hi; rw [actMem]; exact bytes i hi)
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
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0
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
  have finalDelta := NativeTagCheck.native_tail_choice_of_delta real source fetched sp t fin sel enc0 K budget draws
    quiet hook actionDelta nativePrefix tq actionPins enc eret actionIT actionSS (nativePrefix.trans tail)
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (ArmCertMem.LdpEval.ldpPost fetched Rt Rt2 data).regs.gpr := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, ActionTransport.gpr e20]
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, spEq]
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_,⟨draws,finalDelta,drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · refine holds_pair fetched fin _ _ (ArmCertMem.LdpEval.ldpLo data) (ArmCertMem.LdpEval.ldpHi data)
      (by rw [output.gpr, hgT]; rfl) (by rw [output.sp, hspT])
  · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT], by rw [output.sp, hspT], finMem, ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms ldp_one_tailG
def SplitFacts (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  (pairAddr f Rn imm7).toNat % 8 = 0 ∧ (pairAddr f Rn imm7).toNat % 16 ≠ 0 ∧
    ∃ (pa : Fin 2 → BitVec 56) (data : BitVec 128),
      (∀ j : Fin 2, mapping (PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
      (∀ j : Fin 2, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 2, ∀ i < 8, f.mem[(pa j).toNat + i]? = some ((PairSplit.halfValue data j).extractLsb' (8 * i) 8)) ∧
      (∀ acc, DataShape false acc → ∀ j : Fin 2,
        m.permitted (PairSplit.halfAddress (pairAddr f Rn imm7) j) acc true (8 : Int))

def SplitPay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f g : NativeState) : Prop :=
  ∃ (pa : Fin 2 → BitVec 56) (data : BitVec 128),
    (∀ j : Fin 2, mapping (PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
    (∀ j : Fin 2, ∀ i < 8, f.mem[(pa j).toNat + i]? = some ((PairSplit.halfValue data j).extractLsb' (8 * i) 8)) ∧
    g.regs.gpr = (ArmCertMem.LdpEval.ldpPost f Rt Rt2 data).regs.gpr ∧
    g.regs.SP_EL0 = f.regs.SP_EL0 ∧ g.mem = f.mem ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem ldp_split_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) (profile : AccessProfile) (sourcePins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (Ctx spec config rows mapping m catalogue 2 (SplitFacts mapping m imm7 Rn))
      D sel {} K source (source.regs._PC + 4#64)
      [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (SplitPay mapping Rt Rt2 imm7 Rn) 2 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨h8,h16,pa,data,mapped,mmio,bytes,perm⟩ := ctx.prog
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata sel K
  have metadataQuiet := actionState_quiet sel sp K (budget + 1) postS.quiet
  have actionPrefixDelta : ChoiceDelta fetched (actionState sel sp K) 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (NativeTagCheck.spec_choice_of_run (budget+1) fetched sp quiet hook)
      (NativeTagCheck.metadata_choice sel sp K)
  have actionRows := TranslateSpan.DefaultMTE2.rows_after_delta fetched (actionState sel sp K)
    2 2 0 ctx.statusRows actionPrefixDelta (by omega)
  have metaPins := entryPins_at_metadata sp sel K
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := sel) (K := K) postS.mem
  have spEq := ActionTransport.sp0 (w := sel) (K := K) e20
  have gprEq := ActionTransport.gpr (w := sel) (K := K) e20
  have feat := ActionTransport.feat (w := sel) (K := K) e20
  obtain ⟨t,ok,hr,hm,⟨draws,actionDelta,drawBound⟩,_⟩ :=
    LdpSplit.run spec config rows mapping (actionState sel sp K) imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
      profile (profile_of_sys sourcePins metadataInput.sys) (feat ▸ ctx.feat.2.2.2)
      (by simpa only [pairAddr,gprEq] using h8) (by simpa only [pairAddr,gprEq] using h16)
      m (ctx.current.action sel K e20 postS.mem) actionRows pa
      (by intro acc sh j; simpa only [pairAddr,gprEq] using perm acc sh j)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
      (by intro j; simpa only [pairAddr,gprEq] using mapped j) mmio data
      (by intro j i hi; rw [actMem]; exact bytes j i hi)
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
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0
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
  have finalDelta := NativeTagCheck.native_tail_choice_of_delta real source fetched sp t fin sel enc0 K budget draws
    quiet hook actionDelta nativePrefix tq actionPins enc eret actionIT actionSS (nativePrefix.trans tail)
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have hgT : t.regs.gpr = (ArmCertMem.LdpEval.ldpPost fetched Rt Rt2 data).regs.gpr := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, ActionTransport.gpr e20]
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [hr]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, spEq]
  refine ⟨sp, t, fin, fun _ => False, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, fun _ h => h.elim, gic, ?_, nonProj,
    fun a h => by rw [finMem]; exact h, ?_, ?_,⟨draws,finalDelta,drawBound⟩⟩
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  · refine holds_pair fetched fin _ _ (ArmCertMem.LdpEval.ldpLo data) (ArmCertMem.LdpEval.ldpHi data)
      (by rw [output.gpr, hgT]; rfl) (by rw [output.sp, hspT])
  · refine ⟨pa, data, mapped, bytes, by rw [output.gpr, hgT], by rw [output.sp, hspT], finMem, ?_⟩
    have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
    simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
    exact h

#print axioms ldp_split_tailG
end PairDefault236.PairTail
