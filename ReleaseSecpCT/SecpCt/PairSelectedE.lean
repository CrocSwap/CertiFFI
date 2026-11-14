-- secp CT0: event version of Xlate's DefaultPairSelected.ldp_tailG (dispatch one16/two8/bytes by the
-- public VA alignment), over the generated LDP event tails.
import PairDefault236.PairStoreTail
import TranslateSpan.DefaultBudget
import TranslateSpan.DefaultPairValue
import NativeEntryBodyDispatch.Ldp8
import NativeEntryBodyDispatch.Stp8
import TranslateSpan.DefaultPairSelected
import SecpCt.PairTailE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
namespace SecpCt.PairRecs
/-- The request (VA, size) list of the actual LDP path at A (selected by A's alignment: public). -/
def ldpVAS (A : BitVec 64) : List (BitVec 64 × Nat) :=
  match NativeAccess.PairGeometry.selected A with
  | .one16 => oneVAS A
  | .two8 => splitVAS A
  | .bytes => bytesVAS A
end SecpCt.PairRecs

namespace TranslateSpan.CtE.DefaultPairSelected
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open TranslateSpan.DefaultPairSelected
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts ArmCertMemPipe
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv
open NativeAccess
open NativeAccess.LdpBytes NativeAccess.PairGeometry

theorem ldp_tailE (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : PairDefault236.Current.Consumer) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (source : NativeState) (profile : AccessProfile) (pins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (PairDefault236.Ctx spec config rows mapping m catalogue
      (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) (LoadFacts domain mapping m imm7 Rn)) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) {} 611 source (source.regs._PC + 4#64)
      [((.x (RegBind.rk Rt)),.drop),((.x (RegBind.rk Rt2)),.drop)]
      (fun f g => LoadPay mapping Rt Rt2 imm7 Rn f g ∧ ArmCertMemPipe.EvD spec (SecpCt.PairRecs.vaRecs spec false (SecpCt.PairRecs.ldpVAS (pairAddr f Rn imm7))) f g)
      (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) := by
  intro fetched enc0 budget stepPins input guard quiet it ss current ctx
  let sel := NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7
  have dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) 611 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Ldp8.dispatch_at real pc Rt Rn Rt2 imm7 t (by simpa using see)
  have noEret := ldp8_noEret Rt Rn Rt2 imm7
  have addr : pairAddr fetched Rn imm7 = pairAddr source Rn imm7 := by
    simp only [pairAddr, ← input.gpr]
  have statusRows := ctx.statusRows
  rw [← addr] at statusRows
  unfold TranslateSpan.DefaultBudget.cost at statusRows
  have geom := selected_spec (pairAddr fetched Rn imm7)
  have facts := ctx.prog
  simp only [LoadFacts] at facts
  generalize choice : selected (pairAddr fetched Rn imm7) = c at geom facts statusRows
  cases c with
  | one16 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 1 (PairDefault236.PairTail.OneFacts mapping m imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.CtE.PairTail.ldp_one_tailE real domain spec config rows mapping m sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret (fun _ => False) source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [LoadPay,TranslateSpan.DefaultBudget.cost,← addr,choice,SecpCt.PairRecs.ldpVAS,PairDefault236.PairTail.OnePay,PairDefault236.PairTail.SplitPay,PairDefault236.PairTail.BytePay] using run
  | two8 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 2 (PairDefault236.PairTail.SplitFacts mapping m imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom.1,geom.2,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.CtE.PairTail.ldp_split_tailE real domain spec config rows mapping m sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret (fun _ => False) source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [LoadPay,TranslateSpan.DefaultBudget.cost,← addr,choice,SecpCt.PairRecs.ldpVAS,PairDefault236.PairTail.OnePay,PairDefault236.PairTail.SplitPay,PairDefault236.PairTail.BytePay] using run
  | bytes =>
    have not8 : (pairAddr fetched Rn imm7).toNat % 8 ≠ 0 := by
      intro h
      by_cases h16 : (pairAddr fetched Rn imm7).toNat % 16 = 0
      · simp [selected,h16] at choice
      · simp [selected,h16,h] at choice
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 16 (PairDefault236.PairTail.ByteFacts domain mapping m imm7 Rn) fetched :=
      ⟨ctx.current,⟨not8,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.CtE.PairTail.ldp_bytes_tailE real domain spec config rows mapping m sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret (fun _ => False) source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [LoadPay,TranslateSpan.DefaultBudget.cost,← addr,choice,SecpCt.PairRecs.ldpVAS,PairDefault236.PairTail.OnePay,PairDefault236.PairTail.SplitPay,PairDefault236.PairTail.BytePay] using run

theorem ldp_xfer_facts
    (domain : BitVec 64 → Prop) 
    (mapping : BitVec 64 → Option Nat) (m : PairDefault236.Current.Consumer) 
    (imm7 : BitVec 7) (Rn : BitVec 5) {x f : NativeState}
    (gpr : f.regs.gpr = x.regs.gpr) (mem : f.mem = x.mem)
    (facts : LoadFacts domain mapping m imm7 Rn x) : LoadFacts domain mapping m imm7 Rn f := by
  have addr : pairAddr f Rn imm7 = pairAddr x Rn imm7 := by simp only [pairAddr,gpr]
  unfold LoadFacts at facts ⊢
  rw [addr]
  cases choice : selected (pairAddr x Rn imm7) <;> simp only [choice] at facts ⊢
  all_goals simpa only [LoadOneData,LoadSplitData,LoadByteData,pairAddr,gpr,mem] using facts

theorem ldp_xfer_pay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5)
    (imm7 : BitVec 7) (Rn : BitVec 5) {x f g : NativeState}
    (hg : f.regs.gpr = x.regs.gpr) (hs : f.regs.SP_EL0 = x.regs.SP_EL0) (hm : f.mem = x.mem)
    (hz : Flags.nzcv f.regs = Flags.nzcv x.regs)
    (pay : LoadPay mapping Rt Rt2 imm7 Rn f g) : LoadPay mapping Rt Rt2 imm7 Rn x g := by
  have addr : pairAddr f Rn imm7 = pairAddr x Rn imm7 := by simp only [pairAddr,hg]
  unfold LoadPay at pay ⊢
  rw [addr] at pay
  cases choice : selected (pairAddr x Rn imm7) <;> simp only [choice] at pay ⊢
  all_goals
    obtain ⟨pa,data,mp,bytes,gg,gs,gm,gz⟩ := pay
    refine ⟨pa,data,?_,?_,?_,gs.trans hs,gm.trans hm,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using bytes
    · simpa only [ArmCertMem.LdpEval.ldpPost,CryptoMem.MemCore.setGpr,hg] using gg


#print axioms TranslateSpan.CtE.DefaultPairSelected.ldp_tailE
end TranslateSpan.CtE.DefaultPairSelected
