import PairDefault236.PairStoreTail
import TranslateSpan.DefaultBudget
import TranslateSpan.DefaultPairValue
import NativeEntryBodyDispatch.Ldp8
import NativeEntryBodyDispatch.Stp8
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
namespace TranslateSpan.DefaultPairSelected
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts ArmCertMemPipe
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv
open NativeAccess
open NativeAccess.LdpBytes NativeAccess.PairGeometry

theorem ldp8_noEret (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) :
    (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have bit := congrArg (fun v => v.getLsbD 15) h
  simp only [NativeEntryBodyDispatch.Ldp8.selected,NativeEntryBodyDispatch.Ldp8.word,
    Sail.BitVec.extractLsb,BitVec.extractLsb,BitVec.getLsbD_extractLsb',BitVec.getLsbD_append] at bit
  simp at bit

theorem stp8_noEret (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) :
    (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have bit := congrArg (fun v => v.getLsbD 15) h
  simp only [NativeEntryBodyDispatch.Stp8.selected,NativeEntryBodyDispatch.Stp8.word,
    Sail.BitVec.extractLsb,BitVec.extractLsb,BitVec.getLsbD_extractLsb',BitVec.getLsbD_append] at bit
  simp at bit

def LoadOneData (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  ∃ (pa : BitVec 56) (data : BitVec 128),
    mapping (pairAddr f Rn imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    (∀ i < 16, f.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧
    (∀ acc, DataShape false acc → m.permitted (pairAddr f Rn imm7) acc
      (PairDefault236.PairOne.pairAligned (pairAddr f Rn imm7)) (16 : Int))

def LoadSplitData (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  ∃ (pa : Fin 2 → BitVec 56) (data : BitVec 128),
      (∀ j : Fin 2, mapping (PairDefault236.PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
      (∀ j : Fin 2, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 2, ∀ i < 8, f.mem[(pa j).toNat + i]? = some ((PairDefault236.PairSplit.halfValue data j).extractLsb' (8 * i) 8)) ∧
      (∀ acc, DataShape false acc → ∀ j : Fin 2,
        m.permitted (PairDefault236.PairSplit.halfAddress (pairAddr f Rn imm7) j) acc true (8 : Int))

def LoadByteData (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  (∀ j : Fin 16, domain (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int))) ∧
    ∃ (pa : Fin 16 → BitVec 56) (data : BitVec 128),
      (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
      (∀ j : Fin 16, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 16, f.mem[(pa j).toNat]? = some (data.extractLsb' (8 * j.val) 8)) ∧
      (∀ acc, DataShape false acc → ∀ (j : Fin 16) (aligned : Bool),
        m.permitted (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) acc aligned (1 : Int))

def LoadFacts (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => LoadOneData mapping m imm7 Rn x
  | .two8 => LoadSplitData mapping m imm7 Rn x
  | .bytes => LoadByteData domain mapping m imm7 Rn x

def LoadPay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => PairDefault236.PairTail.OnePay mapping Rt Rt2 imm7 Rn x y
  | .two8 => PairDefault236.PairTail.SplitPay mapping Rt Rt2 imm7 Rn x y
  | .bytes => PairDefault236.PairTail.BytePay mapping Rt Rt2 imm7 Rn x y

def StoreOneData {domain : BitVec 64 → Prop} (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  ∃ pa : BitVec 56, mapping (pairAddr f Rn imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      (∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i)) ∧
      (∀ i < 16, D (pa.toNat + i)) ∧
      (∀ acc, DataShape true acc → m.permitted (pairAddr f Rn imm7) acc
        (Logical.accessAligned (pairAddr f Rn imm7) 16 true) (16 : Int))

def StoreSplitData {domain : BitVec 64 → Prop} (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  ∃ pa : Fin 2 → BitVec 56,
      (∀ j : Fin 2, mapping (PairDefault236.PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
      (∀ j : Fin 2, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 2, ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte ((pa j).toNat + i)) ∧
      (∀ j : Fin 2, ∀ i < 8, D ((pa j).toNat + i)) ∧
      (∀ acc, DataShape true acc → ∀ j : Fin 2,
        m.permitted (PairDefault236.PairSplit.halfAddress (pairAddr f Rn imm7) j) acc true (8 : Int))

def StoreByteData (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  (∀ j : Fin 16, domain (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int))) ∧
    ∃ pa : Fin 16 → BitVec 56,
      (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
      (∀ j : Fin 16, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 16, ¬ (rowsFootprint spec.imageRows).byte (pa j).toNat) ∧
      (∀ j : Fin 16, D (pa j).toNat) ∧
      (∀ acc, DataShape true acc → ∀ (j : Fin 16) (aligned : Bool),
        m.permitted (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) acc aligned (1 : Int))

def StoreFacts (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va)) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => StoreOneData spec mapping m D imm7 Rn x
  | .two8 => StoreSplitData spec mapping m D imm7 Rn x
  | .bytes => StoreByteData domain spec mapping m D imm7 Rn x

def StorePay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => PairDefault236.PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn x y
  | .two8 => PairDefault236.PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn x y
  | .bytes => PairDefault236.PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn x y

/-- Physical byte binding for only the actual selected access plan. -/
def Binding (view : ArmCertValue.Physical.BytePA) (r : ArmCertValue.Region) (word : Nat)
    (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => ∀ pa, mapping (pairAddr x Rn imm7) = some pa → ∀ i, i < 16 → view r (8 * word + i) = some (pa + i)
  | .two8 => ∀ (j : Fin 2) pa, mapping (PairDefault236.PairSplit.halfAddress (pairAddr x Rn imm7) j) = some pa →
      ∀ i, i < 8 → view r (8 * word + 8 * j.val + i) = some (pa + i)
  | .bytes => ∀ (j : Fin 16) pa, mapping (BitVec.addInt (pairAddr x Rn imm7) (j.val : Int)) = some pa →
      view r (8 * word + j.val) = some pa

theorem load_flags (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) (pay : LoadPay mapping Rt Rt2 imm7 Rn x y) : Flags.nzcv y.regs = Flags.nzcv x.regs := by
  unfold LoadPay at pay
  generalize choice : selected (pairAddr x Rn imm7) = c at pay
  cases c <;> obtain ⟨_,_,_,_,_,_,_,hz⟩ := pay <;> exact hz

theorem store_flags (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) (pay : StorePay mapping Rt Rt2 imm7 Rn x y) : Flags.nzcv y.regs = Flags.nzcv x.regs := by
  unfold StorePay at pay
  generalize choice : selected (pairAddr x Rn imm7) = c at pay
  cases c <;> obtain ⟨_,_,_,_,_,_,_,_,hz⟩ := pay <;> exact hz

theorem load_value (view : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region)
    (x y : NativeState) (r : ArmCertValue.Region) (word : Nat) (mapping : BitVec 64 → Option Nat)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (binding : Binding view r word mapping imm7 Rn x) (pay : LoadPay mapping Rt Rt2 imm7 Rn x y) :
    ArmCertValue.Physical.MemVHolds view regions
      [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  unfold Binding at binding
  unfold LoadPay at pay
  generalize choice : selected (pairAddr x Rn imm7) = c at binding pay
  cases c with
  | one16 => exact TranslateSpan.DefaultPairValue.ldp_one_value view regions x y r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay
  | two8 => exact TranslateSpan.DefaultPairValue.ldp_split_value view regions x y r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay
  | bytes => exact TranslateSpan.DefaultPairValue.ldp_byte_value view regions x y r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay

#print axioms load_value

theorem store_value (view : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region)
    (x y : NativeState) (r : ArmCertValue.Region) (word : Nat) (mapping : BitVec 64 → Option Nat)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words)
    (injective : ArmCertValue.Physical.RegionsInjective view regions)
    (binding : Binding view r word mapping imm7 Rn x) (pay : StorePay mapping Rt Rt2 imm7 Rn x y) :
    ArmCertValue.Physical.MemVHolds view regions
      [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)] x y := by
  unfold Binding at binding
  unfold StorePay at pay
  generalize choice : selected (pairAddr x Rn imm7) = c at binding pay
  cases c with
  | one16 => exact TranslateSpan.DefaultPairValue.stp_one_value view regions x y r word mapping imm7 Rn Rt Rt2 binding member fits injective pay
  | two8 => exact TranslateSpan.DefaultPairValue.stp_split_value view regions x y r word mapping imm7 Rn Rt Rt2 binding member fits injective pay
  | bytes => exact TranslateSpan.DefaultPairValue.stp_byte_value view regions x y r word mapping imm7 Rn Rt Rt2 binding member fits injective pay

#print axioms store_value


theorem ldp_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : PairDefault236.Current.Consumer) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (source : NativeState) (profile : AccessProfile) (pins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (PairDefault236.Ctx spec config rows mapping m catalogue
      (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) (LoadFacts domain mapping m imm7 Rn)) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) {} 611 source (source.regs._PC + 4#64)
      [((.x (RegBind.rk Rt)),.drop),((.x (RegBind.rk Rt2)),.drop)] (LoadPay mapping Rt Rt2 imm7 Rn) (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) := by
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
    have run := PairDefault236.PairTail.ldp_one_tailG real domain spec config rows mapping m sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret (fun _ => False) source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [LoadPay,TranslateSpan.DefaultBudget.cost,← addr,choice] using run
  | two8 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 2 (PairDefault236.PairTail.SplitFacts mapping m imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom.1,geom.2,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.PairTail.ldp_split_tailG real domain spec config rows mapping m sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret (fun _ => False) source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [LoadPay,TranslateSpan.DefaultBudget.cost,← addr,choice] using run
  | bytes =>
    have not8 : (pairAddr fetched Rn imm7).toNat % 8 ≠ 0 := by
      intro h
      by_cases h16 : (pairAddr fetched Rn imm7).toNat % 16 = 0
      · simp [selected,h16] at choice
      · simp [selected,h16,h] at choice
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 16 (PairDefault236.PairTail.ByteFacts domain mapping m imm7 Rn) fetched :=
      ⟨ctx.current,⟨not8,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.PairTail.ldp_bytes_tailG real domain spec config rows mapping m sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret (fun _ => False) source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [LoadPay,TranslateSpan.DefaultBudget.cost,← addr,choice] using run

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

#print axioms ldp_tailG
#print axioms ldp_xfer_facts
#print axioms ldp_xfer_pay

theorem stp_tailG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : PairDefault236.Current.Consumer) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (D : Nat → Prop)
    (source : NativeState) (profile : AccessProfile) (pins : ProfileAt profile source) :
    TranslateSpan.DefaultEntryMem.MemTailAt real spec config rows (PairDefault236.Ctx spec config rows mapping m catalogue
      (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) (StoreFacts domain spec mapping m D imm7 Rn)) D
      (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) {} 617 source (source.regs._PC + 4#64)
      [] (StorePay mapping Rt Rt2 imm7 Rn) (TranslateSpan.DefaultBudget.cost (pairAddr source Rn imm7)) := by
  intro fetched enc0 budget stepPins input guard quiet it ss current ctx
  let sel := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7
  have dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) 617 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Stp8.dispatch_at real pc Rt Rn Rt2 imm7 t (by simpa using see)
  have noEret := stp8_noEret Rt Rn Rt2 imm7
  have addr : pairAddr fetched Rn imm7 = pairAddr source Rn imm7 := by
    simp only [pairAddr, ← input.gpr]
  have statusRows := ctx.statusRows
  rw [← addr] at statusRows
  unfold TranslateSpan.DefaultBudget.cost at statusRows
  have geom := selected_spec (pairAddr fetched Rn imm7)
  have facts := ctx.prog
  simp only [StoreFacts] at facts
  generalize choice : selected (pairAddr fetched Rn imm7) = c at geom facts statusRows
  cases c with
  | one16 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 1 (PairDefault236.PairStoreTail.OneFacts spec mapping m D imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.PairStoreTail.stp_one_tailG real domain spec config rows mapping m sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret D source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [StorePay,TranslateSpan.DefaultBudget.cost,← addr,choice] using run
  | two8 =>
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 2 (PairDefault236.PairStoreTail.SplitFacts spec mapping m D imm7 Rn) fetched :=
      ⟨ctx.current,⟨geom.1,geom.2,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.PairStoreTail.stp_split_tailG real domain spec config rows mapping m sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret D source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [StorePay,TranslateSpan.DefaultBudget.cost,← addr,choice] using run
  | bytes =>
    have not8 : (pairAddr fetched Rn imm7).toNat % 8 ≠ 0 := by
      intro h
      by_cases h16 : (pairAddr fetched Rn imm7).toNat % 16 = 0
      · simp [selected,h16] at choice
      · simp [selected,h16,h] at choice
    have fc : PairDefault236.Ctx spec config rows mapping m catalogue 16 (PairDefault236.PairStoreTail.ByteFacts domain spec mapping m D imm7 Rn) fetched :=
      ⟨ctx.current,⟨not8,facts⟩,ctx.feat,statusRows⟩
    have run := PairDefault236.PairStoreTail.stp_bytes_tailG real domain spec config rows mapping m sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret D source profile pins
      fetched enc0 budget stepPins input guard quiet it ss current fc
    simpa only [StorePay,TranslateSpan.DefaultBudget.cost,← addr,choice] using run

theorem stp_xfer_facts
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : PairDefault236.Current.Consumer) (D : Nat → Prop)
    (imm7 : BitVec 7) (Rn : BitVec 5) {x f : NativeState}
    (gpr : f.regs.gpr = x.regs.gpr) (mem : f.mem = x.mem)
    (facts : StoreFacts domain spec mapping m D imm7 Rn x) : StoreFacts domain spec mapping m D imm7 Rn f := by
  have addr : pairAddr f Rn imm7 = pairAddr x Rn imm7 := by simp only [pairAddr,gpr]
  unfold StoreFacts at facts ⊢
  rw [addr]
  cases choice : selected (pairAddr x Rn imm7) <;> simp only [choice] at facts ⊢
  all_goals simpa only [StoreOneData,StoreSplitData,StoreByteData,pairAddr,gpr,mem] using facts

theorem stp_xfer_pay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5)
    (imm7 : BitVec 7) (Rn : BitVec 5) {x f g : NativeState}
    (hg : f.regs.gpr = x.regs.gpr) (hs : f.regs.SP_EL0 = x.regs.SP_EL0) (hm : f.mem = x.mem)
    (hz : Flags.nzcv f.regs = Flags.nzcv x.regs)
    (pay : StorePay mapping Rt Rt2 imm7 Rn f g) : StorePay mapping Rt Rt2 imm7 Rn x g := by
  have addr : pairAddr f Rn imm7 = pairAddr x Rn imm7 := by simp only [pairAddr,hg]
  unfold StorePay at pay ⊢
  rw [addr] at pay
  cases choice : selected (pairAddr x Rn imm7) <;> simp only [choice] at pay ⊢
  all_goals
    obtain ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩ := pay
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload

#print axioms stp_tailG
#print axioms stp_xfer_facts
#print axioms stp_xfer_pay
end TranslateSpan.DefaultPairSelected
