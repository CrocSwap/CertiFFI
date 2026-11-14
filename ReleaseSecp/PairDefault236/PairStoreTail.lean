import PairDefault236.StpOne
import PairDefault236.StpSplit
import PairDefault236.StpBytes
import PairDefault236.PairTail
import PairDefault236.Fragments
import ArmCertValue.NativeFragments
import HeapV2StepCerts.C3Byte
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open NativeAccess
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace PairDefault236.PairStoreTail
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded HeapV2StepCerts ArmCertMemPipe
open ArmCert.HookQuiet.V0 (HookQuiet)
open PairDefault236.Trace
open TranslateSpan.DefaultAccessTrace NativeMteTagCheck
open NativeAccess.Trace (Access)
open NativeAccess.LdpBytes
open PairDefault236.PairTail (profile_of_sys)
open PairDefault236.Fragments
attribute [local implicit_reducible] EStateM Arch.arch_ak

theorem frames (a u : NativeState) (hr : u.regs = a.regs) :
    ActFrame a u ∧ ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs u.regs ∧
    u.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
    u.regs.PhysicalCount = a.regs.PhysicalCount := by
  refine ⟨?_,?_,?_,?_⟩
  · constructor <;> rw [hr]
  · rw [hr]; rfl
  · rw [hr]
  · rw [hr]

theorem writeMemory_isSome (calls : List WriteCall) (mem : Std.ExtHashMap Nat (BitVec 8))
    (a : Nat) (h : mem[a]?.isSome) : (writeMemory calls mem)[a]?.isSome := by
  induction calls generalizing mem with
  | nil => exact h
  | cons c cs ih => exact ih _ (MemTail.wfold_isSome _ _ _ _ _ h)

def OneFacts {domain : BitVec 64 → Prop} (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  NativeMte2.Read.Within16 (pairAddr f Rn imm7) ((16 : Nat) : Int) ∧
    ∃ pa : BitVec 56, mapping (pairAddr f Rn imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      (∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i)) ∧
      (∀ i < 16, D (pa.toNat + i)) ∧
      (∀ acc, DataShape true acc → m.permitted (pairAddr f Rn imm7) acc
        (Logical.accessAligned (pairAddr f Rn imm7) 16 true) (16 : Int))

def OnePay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f g : NativeState) : Prop :=
  ∃ (pa : BitVec 56) (calls : List WriteCall), mapping (pairAddr f Rn imm7) = some pa.toNat ∧
    g.mem = writeMemory calls f.mem ∧
    (∃ acc, calls.map WriteCall.request = [⟨0,pairAddr f Rn imm7,16,acc,
      Logical.accessAligned (pairAddr f Rn imm7) 16 true,true⟩]) ∧
    (∀ call ∈ calls, call.request.offset = 0 ∧ call.request.bytes = 16 ∧ call.packet.ad.paddress.address = pa ∧
      (Sail.BitVec.castWidth call.packet.data : BitVec 128) = ArmCertMem.StpEval.stpData f Rt Rt2) ∧
    g.regs.gpr = f.regs.gpr ∧ g.regs.SP_EL0 = f.regs.SP_EL0 ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem stp_one_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) (profile : AccessProfile) (sourcePins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (Ctx spec config rows mapping m catalogue 1 (OneFacts spec mapping m D imm7 Rn))
      D sel {} K source (source.regs._PC + 4#64)
      [] (OnePay mapping Rt Rt2 imm7 Rn) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨fit,pa,mapped,mmio,outside,inD,perm⟩ := ctx.prog
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
  obtain ⟨t,ok,hr,⟨draws,actionDelta,drawBound⟩,memEnd,calls,actualAcc,chain,hm,he,requests,payload⟩ :=
    StpOne.run spec config rows mapping (actionState sel sp K) imm7 Rn Rt Rt2 hRn hRt hRt2
      profile (profile_of_sys sourcePins metadataInput.sys) (feat ▸ ctx.feat.2.2.2)
      (Control.natural_of_fit _ (by simpa [pairAddr,gprEq] using fit))
      (by simpa only [pairAddr,gprEq] using fit)
      m (ctx.current.action sel K e20 postS.mem) actionRows
      (by intro acc sh; simpa only [pairAddr,gprEq] using perm acc sh)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
      pa (by simpa only [pairAddr,gprEq] using mapped) mmio
  obtain ⟨af,npe,gic0,ph⟩ := frames _ t hr
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
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0
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
  have finMem : fin.mem = writeMemory calls fetched.mem := by
    rw [output.mem,hm,chain.memory,actMem]
  have hgT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact gprEq
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by rw [hr]; exact spEq
  have sizes : ∀ c ∈ calls, c.request.bytes = 16 := by
    intro c hc
    have h : c.request ∈ calls.map WriteCall.request := List.mem_map.mpr ⟨c,hc,rfl⟩
    rw [requests,List.mem_singleton] at h
    exact congrArg Access.bytes h
  have windows : ∀ x, ArmCertValue.SplitMemory.Writes (writeSegments calls) x →
      ¬ (rowsFootprint spec.imageRows).byte x ∧ D x := by
    intro x ⟨seg,hs,lo,hi⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
    have hp := (payload c hc).1
    change c.packet.ad.paddress.address.toNat ≤ x at lo
    change x < c.packet.ad.paddress.address.toNat + c.request.bytes at hi
    rw [hp] at lo hi
    rw [sizes c hc] at hi
    have eqx : pa.toNat + (x-pa.toNat) = x := by omega
    exact ⟨by simpa only [eqx] using outside (x-pa.toNat) (by omega),
      by simpa only [eqx] using inD (x-pa.toNat) (by omega)⟩
  refine ⟨sp,t,fin,ArmCertValue.SplitMemory.Writes (writeSegments calls),hook,nativePrefix.trans tail,frame,
    finalQuiet,finalPins,sys,?_,?_,?_,gic,?_,nonProj,?_,?_,?_,⟨draws,finalDelta,drawBound⟩⟩
  · intro a ha
    show fin.mem[a]? = fetched.mem[a]?
    rw [output.mem,hm]
    exact (writeChain_frame chain a ha).trans (congrArg (fun mem => mem[a]?) actMem)
  · intro a ha hw; exact (windows a hw).1 ha
  · intro a hw; exact (windows a hw).2
  · simpa only [noBranch,Bool.false_eq_true,ite_false,actionPC] using pc
  · intro a h; rw [finMem]; exact writeMemory_isSome calls fetched.mem a h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr,hgT]) (by rw [output.sp,hspT])
  · refine ⟨pa,calls,mapped,finMem,⟨actualAcc,by simpa only [pairAddr,gprEq] using requests⟩,?_,by rw [output.gpr,hgT],by rw [output.sp,hspT],?_⟩
    · intro c hc
      have h : c.request ∈ calls.map WriteCall.request := List.mem_map.mpr ⟨c,hc,rfl⟩
      rw [requests,List.mem_singleton] at h
      refine ⟨congrArg Access.offset h,sizes c hc,(payload c hc).1,?_⟩
      simpa only [ArmCertMem.StpEval.stpData,gprEq] using (payload c hc).2
    ·
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h

#print axioms stp_one_tailG
def SplitFacts {domain : BitVec 64 → Prop} (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  (pairAddr f Rn imm7).toNat % 8 = 0 ∧ (pairAddr f Rn imm7).toNat % 16 ≠ 0 ∧
    ∃ pa : Fin 2 → BitVec 56,
      (∀ j : Fin 2, mapping (PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
      (∀ j : Fin 2, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 2, ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte ((pa j).toNat + i)) ∧
      (∀ j : Fin 2, ∀ i < 8, D ((pa j).toNat + i)) ∧
      (∀ acc, DataShape true acc → ∀ j : Fin 2,
        m.permitted (PairSplit.halfAddress (pairAddr f Rn imm7) j) acc true (8 : Int))

def SplitPay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f g : NativeState) : Prop :=
  ∃ (pa : Fin 2 → BitVec 56) (calls : List WriteCall),
    (∀ j : Fin 2, mapping (PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
    g.mem = writeMemory calls f.mem ∧
    (∃ acc, calls.map WriteCall.request = [⟨0,pairAddr f Rn imm7,8,acc,true,false⟩,
      ⟨8,BitVec.addInt (pairAddr f Rn imm7) ((8 : Nat) : Int),8,acc,true,false⟩]) ∧
    (∀ call ∈ calls, ∃ j : Fin 2, call.request.offset = 8 * j.val ∧ call.request.bytes = 8 ∧
      call.packet.ad.paddress.address = pa j ∧ (Sail.BitVec.castWidth call.packet.data : BitVec 64) =
        PairSplit.halfValue (ArmCertMem.StpEval.stpData f Rt Rt2) j) ∧
    g.regs.gpr = f.regs.gpr ∧ g.regs.SP_EL0 = f.regs.SP_EL0 ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem stp_split_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) (profile : AccessProfile) (sourcePins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (Ctx spec config rows mapping m catalogue 2 (SplitFacts spec mapping m D imm7 Rn))
      D sel {} K source (source.regs._PC + 4#64)
      [] (SplitPay mapping Rt Rt2 imm7 Rn) 2 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨h8,h16,pa,mapped,mmio,outside,inD,perm⟩ := ctx.prog
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
  obtain ⟨t,ok,hr,⟨draws,actionDelta,drawBound⟩,memEnd,calls,actualAcc,chain,hm,he,requests,payload⟩ :=
    StpSplit.run spec config rows mapping (actionState sel sp K) imm7 Rn Rt Rt2 hRn hRt hRt2
      profile (profile_of_sys sourcePins metadataInput.sys) (feat ▸ ctx.feat.2.2.2)
      (by simpa only [pairAddr,gprEq] using h8) (by simpa only [pairAddr,gprEq] using h16)
      m (ctx.current.action sel K e20 postS.mem) actionRows pa
      (by intro acc sh j; simpa only [pairAddr,gprEq] using perm acc sh j)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
      (by intro j; simpa only [pairAddr,gprEq] using mapped j) mmio outside
  obtain ⟨af,npe,gic0,ph⟩ := frames _ t hr
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
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0
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
  have finMem : fin.mem = writeMemory calls fetched.mem := by
    rw [output.mem,hm,chain.memory,actMem]
  have hgT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact gprEq
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by rw [hr]; exact spEq
  have windows : ∀ x, ArmCertValue.SplitMemory.Writes (writeSegments calls) x →
      ¬ (rowsFootprint spec.imageRows).byte x ∧ D x := by
    intro x ⟨seg,hs,lo,hi⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
    obtain ⟨j,req,hp,hvalue⟩ := payload c hc
    have sizeEq : c.request.bytes = 8 := congrArg Access.bytes req
    change c.packet.ad.paddress.address.toNat ≤ x at lo
    change x < c.packet.ad.paddress.address.toNat + c.request.bytes at hi
    rw [hp] at lo hi
    rw [sizeEq] at hi
    have eqx : (pa j).toNat + (x-(pa j).toNat) = x := by omega
    exact ⟨by simpa only [eqx] using outside j (x-(pa j).toNat) (by omega),
      by simpa only [eqx] using inD j (x-(pa j).toNat) (by omega)⟩
  refine ⟨sp,t,fin,ArmCertValue.SplitMemory.Writes (writeSegments calls),hook,nativePrefix.trans tail,frame,
    finalQuiet,finalPins,sys,?_,?_,?_,gic,?_,nonProj,?_,?_,?_,⟨draws,finalDelta,drawBound⟩⟩
  · intro a ha
    show fin.mem[a]? = fetched.mem[a]?
    rw [output.mem,hm]
    exact (writeChain_frame chain a ha).trans (congrArg (fun mem => mem[a]?) actMem)
  · intro a ha hw; exact (windows a hw).1 ha
  · intro a hw; exact (windows a hw).2
  · simpa only [noBranch,Bool.false_eq_true,ite_false,actionPC] using pc
  · intro a h; rw [finMem]; exact writeMemory_isSome calls fetched.mem a h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr,hgT]) (by rw [output.sp,hspT])
  · refine ⟨pa,calls,mapped,finMem,⟨actualAcc,by simpa only [pairAddr,gprEq] using requests⟩,?_,by rw [output.gpr,hgT],by rw [output.sp,hspT],?_⟩
    · intro c hc
      obtain ⟨j,req,hp,hvalue⟩ := payload c hc
      refine ⟨j,by simpa only [pairAddr,gprEq] using congrArg Access.offset req,
        congrArg Access.bytes req,hp,?_⟩
      simpa only [ArmCertMem.StpEval.stpData,gprEq] using hvalue
    ·
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h

#print axioms stp_split_tailG
def ByteFacts (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  (pairAddr f Rn imm7).toNat % 8 ≠ 0 ∧
    (∀ j : Fin 16, domain (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int))) ∧
    ∃ pa : Fin 16 → BitVec 56,
      (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
      (∀ j : Fin 16, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 16, ¬ (rowsFootprint spec.imageRows).byte (pa j).toNat) ∧
      (∀ j : Fin 16, D (pa j).toNat) ∧
      (∀ acc, DataShape true acc → ∀ (j : Fin 16) (aligned : Bool),
        m.permitted (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) acc aligned (1 : Int))

def BytePay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f g : NativeState) : Prop :=
  ∃ (pa : Fin 16 → BitVec 56) (calls : List WriteCall),
    (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
    g.mem = writeMemory calls f.mem ∧
    (∃ acc aligned, calls.map WriteCall.request = Loops.byteAccess 0 (pairAddr f Rn imm7) acc false 0 ::
      (List.range' 1 15).map (Loops.byteAccess 0 (pairAddr f Rn imm7) acc aligned)) ∧
    (∀ c ∈ calls, ∃ j : Fin 16, c.request.offset = j.val ∧ c.request.bytes = 1 ∧
      c.packet.ad.paddress.address = pa j ∧ (Sail.BitVec.castWidth c.packet.data : BitVec 8) =
        (ArmCertMem.StpEval.stpData f Rt Rt2).extractLsb' (8 * j.val) 8) ∧
    g.regs.gpr = f.regs.gpr ∧ g.regs.SP_EL0 = f.regs.SP_EL0 ∧ Flags.nzcv g.regs = Flags.nzcv f.regs

theorem stp_bytes_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (source : NativeState) (profile : AccessProfile) (sourcePins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows
      (Ctx spec config rows mapping m catalogue 16 (ByteFacts domain spec mapping m D imm7 Rn)) D sel {} K
      source (source.regs._PC + 4#64)
      [] (BytePay mapping Rt Rt2 imm7 Rn) 16 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨not8,member,pa,mapped,mmio,outside,inD,perm⟩ := ctx.prog
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
  obtain ⟨t,ok,hr,⟨draws,actionDelta,drawBound⟩,memEnd,calls,actualAcc,actualAligned,chain,hm,he,requests,payload⟩ :=
    StpBytes.run spec config rows mapping (actionState sel sp K) imm7 Rn Rt Rt2 hRn hRt hRt2
      profile (profile_of_sys sourcePins metadataInput.sys) (feat ▸ ctx.feat.2.2.2)
      (PairGeometry.pairAligned_false _ not8A) (PairGeometry.join_disabled _ _ not16A)
      m (ctx.current.action sel K e20 postS.mem) actionRows pa
      (by intro acc sh j al; simpa only [pairAddr,gprEq] using perm acc sh j al)
      (feat ▸ ctx.feat.1) (feat ▸ ctx.feat.2.1) (feat ▸ ctx.feat.2.2.1)
      (by intro j; simpa only [pairAddr,gprEq] using mapped j) mmio outside
  obtain ⟨af,npe,gic0,ph⟩ := frames _ t hr
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
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0 sp currentGuard K hK dispatch
  have nativePrefix : nativeTail real source sel enc0 fetched = nativeAfterAction real source sel enc0 t := by
    calc
      nativeTail real source sel enc0 fetched = afterSpecPmu real source sel enc0 sp :=
        spec_pmu_boundary real source sel enc0 fetched sp hook
      _ = nativeAtAction real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0
          (actionState sel sp K) := boundary
      _ = nativeAfterAction real source sel enc0 t :=
        action_boundary real source sel
          (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0
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
  have finMem : fin.mem = writeMemory calls fetched.mem := by
    rw [output.mem,hm,chain.memory,actMem]
  have hgT : t.regs.gpr = fetched.regs.gpr := by rw [hr]; exact gprEq
  have hspT : t.regs.SP_EL0 = fetched.regs.SP_EL0 := by rw [hr]; exact spEq
  have packetData : ∀ c ∈ calls, ∃ j : Fin 16,
      c.request.offset = j.val ∧ c.request.bytes = 1 ∧ c.packet.ad.paddress.address = pa j ∧
      (Sail.BitVec.castWidth c.packet.data : BitVec 8) =
        (ArmCertMem.StpEval.stpData fetched Rt Rt2).extractLsb' (8 * j.val) 8 := by
    intro c hc
    have witness := payload c hc
    rcases witness with witness | witness
    all_goals
      obtain ⟨j,hlo,hhi,req,hp,hvalue⟩ := witness
      refine ⟨j,?_,?_,hp,?_⟩
      · simpa only [Loops.byteAccess,Nat.zero_add] using congrArg Access.offset req
      · exact congrArg Access.bytes req
      · simpa only [ArmCertMem.StpEval.stpData,gprEq] using hvalue
  have windows : ∀ x, ArmCertValue.SplitMemory.Writes (writeSegments calls) x →
      ¬ (rowsFootprint spec.imageRows).byte x ∧ D x := by
    intro x ⟨seg,hs,lo,hi⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
    obtain ⟨j,off,size,hp,hvalue⟩ := packetData c hc
    change c.packet.ad.paddress.address.toNat ≤ x at lo
    change x < c.packet.ad.paddress.address.toNat + c.request.bytes at hi
    rw [hp] at lo hi
    rw [size] at hi
    have eqx : x = (pa j).toNat := by omega
    subst x
    exact ⟨outside j,inD j⟩
  refine ⟨sp,t,fin,ArmCertValue.SplitMemory.Writes (writeSegments calls),hook,nativePrefix.trans tail,frame,
    finalQuiet,finalPins,sys,?_,?_,?_,gic,?_,nonProj,?_,?_,?_,⟨draws,finalDelta,drawBound⟩⟩
  · intro a ha
    show fin.mem[a]? = fetched.mem[a]?
    rw [output.mem,hm]
    exact (writeChain_frame chain a ha).trans (congrArg (fun mem => mem[a]?) actMem)
  · intro a ha hw; exact (windows a hw).1 ha
  · intro a hw; exact (windows a hw).2
  · simpa only [noBranch,Bool.false_eq_true,ite_false,actionPC] using pc
  · intro a h; rw [finMem]; exact writeMemory_isSome calls fetched.mem a h
  · exact RegBind.holds_of_regs_eq (fun _ => Or.inl rfl) (by rw [output.gpr,hgT]) (by rw [output.sp,hspT])
  · refine ⟨pa,calls,mapped,finMem,⟨actualAcc,actualAligned,?_⟩,packetData,
      by rw [output.gpr,hgT],by rw [output.sp,hspT],?_⟩
    · simpa only [pairAddr,gprEq] using requests
    ·
      have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20
      simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]
      exact h

#print axioms stp_bytes_tailG
end PairDefault236.PairStoreTail
