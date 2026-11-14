import NativeAccess.PairDispatch
import ArmCertStepV.Core
import NativeEntryBodyDispatch.Ldp8
import NativeEntryBodyDispatch.Stp8
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
namespace NativeAccess.PairSelected
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts ArmCertMemPipe
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv
open NativeAccess.LdpBytes PairGeometry

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
      (PairOne.pairAligned (pairAddr f Rn imm7)) ((16 : Nat) : Int))

def LoadSplitData (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  ∃ (pa : Fin 2 → BitVec 56) (data : BitVec 128),
      (∀ j : Fin 2, mapping (PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
      (∀ j : Fin 2, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 2, ∀ i < 8, f.mem[(pa j).toNat + i]? = some ((PairSplit.halfValue data j).extractLsb' (8 * i) 8)) ∧
      (∀ acc, DataShape false acc → ∀ j : Fin 2,
        m.permitted (PairSplit.halfAddress (pairAddr f Rn imm7) j) acc true ((8 : Nat) : Int))

def LoadByteData (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5)
    (f : NativeState) : Prop :=
  (∀ j : Fin 16, domain (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int))) ∧
    ∃ (pa : Fin 16 → BitVec 56) (data : BitVec 128),
      (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
      (∀ j : Fin 16, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 16, f.mem[(pa j).toNat]? = some (data.extractLsb' (8 * j.val) 8)) ∧
      (∀ acc, DataShape false acc → ∀ j : Fin 16,
        m.permitted (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) acc false ((1 : Nat) : Int))

def LoadFacts (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => LoadOneData mapping m imm7 Rn x
  | .two8 => LoadSplitData mapping m imm7 Rn x
  | .bytes => LoadByteData domain mapping m imm7 Rn x

def LoadPay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => PairTail.OnePay mapping Rt Rt2 imm7 Rn x y
  | .two8 => PairTail.SplitPay mapping Rt Rt2 imm7 Rn x y
  | .bytes => PairTail.BytePay mapping Rt Rt2 imm7 Rn x y

theorem ldp_nextG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (facts : LoadFacts domain mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun _ => False) (LoadPay mapping Rt Rt2 imm7 Rn) x fin := by
  let sel := NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7
  have dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) 611 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Ldp8.dispatch_at real pc Rt Rn Rt2 imm7 t (by simpa using see)
  have noEret := ldp8_noEret Rt Rn Rt2 imm7
  have geom := selected_spec (pairAddr x Rn imm7)
  simp only [LoadFacts] at facts
  generalize choice : selected (pairAddr x Rn imm7) = c at geom facts
  cases c with
  | one16 =>
    have fs : PairTail.OneFacts mapping m imm7 Rn x := ⟨geom,facts⟩
    obtain ⟨fin,run,packet⟩ := PairDispatch.ldp_one_nextG real domain spec config rows mapping m
      scope image loadBase separated base offset budget extra k room page aligned sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret x inv profile pins 
      fs nextPlaced obligations
    refine ⟨fin,run,?_⟩
    simpa only [PairNext.Packet,LoadPay,choice] using packet
  | two8 =>
    have fs : PairTail.SplitFacts mapping m imm7 Rn x := ⟨geom.1,geom.2,facts⟩
    obtain ⟨fin,run,packet⟩ := PairDispatch.ldp_split_nextG real domain spec config rows mapping m
      scope image loadBase separated base offset budget extra k room page aligned sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret x inv profile pins 
      fs nextPlaced obligations
    refine ⟨fin,run,?_⟩
    simpa only [PairNext.Packet,LoadPay,choice] using packet
  | bytes =>
    have not8 : (pairAddr x Rn imm7).toNat % 8 ≠ 0 := by
      intro h
      by_cases h16 : (pairAddr x Rn imm7).toNat % 16 = 0
      · simp [selected,h16] at choice
      · simp [selected,h16,h] at choice
    have fs : PairTail.ByteFacts domain mapping m imm7 Rn x := ⟨not8,facts⟩
    obtain ⟨fin,run,packet⟩ := PairDispatch.ldp_bytes_nextG real domain spec config rows mapping m
      scope image loadBase separated base offset budget extra k room page aligned sel 611 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt dispatch noEret x inv profile pins 
      fs nextPlaced obligations
    refine ⟨fin,run,?_⟩
    simpa only [PairNext.Packet,LoadPay,choice] using packet

#print axioms ldp_nextG

def StoreOneData {domain : BitVec 64 → Prop} (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  ∃ pa : BitVec 56, mapping (pairAddr f Rn imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      (∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i)) ∧
      (∀ i < 16, D (pa.toNat + i)) ∧
      (∀ acc, DataShape true acc → m.permitted (pairAddr f Rn imm7) acc
        (Logical.accessAligned (pairAddr f Rn imm7) 16 true) ((16 : Nat) : Int))

def StoreSplitData {domain : BitVec 64 → Prop} (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  ∃ pa : Fin 2 → BitVec 56,
      (∀ j : Fin 2, mapping (PairSplit.halfAddress (pairAddr f Rn imm7) j) = some (pa j).toNat) ∧
      (∀ j : Fin 2, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 2, ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte ((pa j).toNat + i)) ∧
      (∀ j : Fin 2, ∀ i < 8, D ((pa j).toNat + i)) ∧
      (∀ acc, DataShape true acc → ∀ j : Fin 2,
        m.permitted (PairSplit.halfAddress (pairAddr f Rn imm7) j) acc true ((8 : Nat) : Int))

def StoreByteData (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (f : NativeState) : Prop :=
  (∀ j : Fin 16, domain (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int))) ∧
    ∃ pa : Fin 16 → BitVec 56,
      (∀ j : Fin 16, mapping (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) = some (pa j).toNat) ∧
      (∀ j : Fin 16, MemM1.MemReadIF.NotMMIO (pa j)) ∧
      (∀ j : Fin 16, ¬ (rowsFootprint spec.imageRows).byte (pa j).toNat) ∧
      (∀ j : Fin 16, D (pa j).toNat) ∧
      (∀ acc, DataShape true acc → ∀ j : Fin 16,
        m.permitted (BitVec.addInt (pairAddr f Rn imm7) (j.val : Int)) acc false ((1 : Nat) : Int))

def StoreFacts (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va)) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (D : Nat → Prop) (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => StoreOneData spec mapping m D imm7 Rn x
  | .two8 => StoreSplitData spec mapping m D imm7 Rn x
  | .bytes => StoreByteData domain spec mapping m D imm7 Rn x

def StorePay (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn x y
  | .two8 => PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn x y
  | .bytes => PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn x y

theorem stp_nextG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : StoreFacts domain spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [] D (StorePay mapping Rt Rt2 imm7 Rn) x fin := by
  let sel := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7
  have dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) 617 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Stp8.dispatch_at real pc Rt Rn Rt2 imm7 t (by simpa using see)
  have noEret := stp8_noEret Rt Rn Rt2 imm7
  have geom := selected_spec (pairAddr x Rn imm7)
  simp only [StoreFacts] at facts
  generalize choice : selected (pairAddr x Rn imm7) = c at geom facts
  cases c with
  | one16 =>
    have fs : PairStoreTail.OneFacts spec mapping m D imm7 Rn x := ⟨geom,facts⟩
    obtain ⟨fin,run,packet⟩ := PairDispatch.stp_one_nextG real domain spec config rows mapping m
      scope image loadBase separated base offset budget extra k room page aligned sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret x inv profile pins D codeD 
      fs nextPlaced obligations
    refine ⟨fin,run,?_⟩
    simpa only [PairNext.Packet,StorePay,choice] using packet
  | two8 =>
    have fs : PairStoreTail.SplitFacts spec mapping m D imm7 Rn x := ⟨geom.1,geom.2,facts⟩
    obtain ⟨fin,run,packet⟩ := PairDispatch.stp_split_nextG real domain spec config rows mapping m
      scope image loadBase separated base offset budget extra k room page aligned sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret x inv profile pins D codeD 
      fs nextPlaced obligations
    refine ⟨fin,run,?_⟩
    simpa only [PairNext.Packet,StorePay,choice] using packet
  | bytes =>
    have not8 : (pairAddr x Rn imm7).toNat % 8 ≠ 0 := by
      intro h
      by_cases h16 : (pairAddr x Rn imm7).toNat % 16 = 0
      · simp [selected,h16] at choice
      · simp [selected,h16,h] at choice
    have fs : PairStoreTail.ByteFacts domain spec mapping m D imm7 Rn x := ⟨not8,facts⟩
    obtain ⟨fin,run,packet⟩ := PairDispatch.stp_bytes_nextG real domain spec config rows mapping m
      scope image loadBase separated base offset budget extra k room page aligned sel 617 (by decide)
      imm7 Rn Rt Rt2 hRn hRt hRt2 dispatch noEret x inv profile pins D codeD 
      fs nextPlaced obligations
    refine ⟨fin,run,?_⟩
    simpa only [PairNext.Packet,StorePay,choice] using packet

#print axioms stp_nextG

/-- Physical byte binding for only the actual selected access plan. -/
def Binding (view : ArmCertValue.Physical.BytePA) (r : ArmCertValue.Region) (word : Nat)
    (mapping : BitVec 64 → Option Nat) (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState) : Prop :=
  match selected (pairAddr x Rn imm7) with
  | .one16 => ∀ pa, mapping (pairAddr x Rn imm7) = some pa → ∀ i, i < 16 → view r (8 * word + i) = some (pa + i)
  | .two8 => ∀ (j : Fin 2) pa, mapping (PairSplit.halfAddress (pairAddr x Rn imm7) j) = some pa →
      ∀ i, i < 8 → view r (8 * word + 8 * j.val + i) = some (pa + i)
  | .bytes => ∀ (j : Fin 16) pa, mapping (BitVec.addInt (pairAddr x Rn imm7) (j.val : Int)) = some pa →
      view r (8 * word + j.val) = some pa

theorem load_flags (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) (pay : LoadPay mapping Rt Rt2 imm7 Rn x y) : Flags.nzcv y.regs = Flags.nzcv x.regs := by
  unfold LoadPay at pay
  generalize choice : selected (pairAddr x Rn imm7) = c at pay
  cases c <;> obtain ⟨_,_,_,_,_,_,_,hz⟩ := pay <;> exact hz

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
  | one16 => exact PairValue.ldp_one_value view regions x y r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay
  | two8 => exact PairValue.ldp_split_value view regions x y r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay
  | bytes => exact PairValue.ldp_byte_value view regions x y r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay

#print axioms load_value

theorem store_flags (mapping : BitVec 64 → Option Nat) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (Rn : BitVec 5)
    (x y : NativeState) (pay : StorePay mapping Rt Rt2 imm7 Rn x y) : Flags.nzcv y.regs = Flags.nzcv x.regs := by
  unfold StorePay at pay
  generalize choice : selected (pairAddr x Rn imm7) = c at pay
  cases c <;> obtain ⟨_,_,_,_,_,_,_,_,hz⟩ := pay <;> exact hz

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
  | one16 => exact PairValue.stp_one_value view regions x y r word mapping imm7 Rn Rt Rt2 binding member fits injective pay
  | two8 => exact PairValue.stp_split_value view regions x y r word mapping imm7 Rn Rt Rt2 binding member fits injective pay
  | bytes => exact PairValue.stp_byte_value view regions x y r word mapping imm7 Rn Rt Rt2 binding member fits injective pay

#print axioms store_value

theorem ldp_stepV (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (facts : LoadFacts domain mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (view : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region)
    (r : ArmCertValue.Region) (word : Nat) (binding : Binding view r word mapping imm7 Rn x)
    (vus : List (RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)])
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun _ => False) (LoadPay mapping Rt Rt2 imm7 Rn) x fin ∧
      ArmCertValue.Physical.MemVHolds view regions
        [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)] x fin ∧
      ArmCertValue.VHolds vus none x fin ∧ ProfileAt profile fin := by
  obtain ⟨fin,run,packet⟩ := ldp_nextG real domain spec config rows mapping m scope image loadBase separated
    base offset budget extra k room page aligned imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt x inv profile pins facts nextPlaced obligations
  obtain ⟨ps,quiet,current,pc,debug,feat,gic,closed,placed,branch,holds,writes,pay,pres,sys⟩ := packet
  refine ⟨fin,run,⟨ps,quiet,current,pc,debug,feat,gic,closed,placed,branch,holds,writes,pay,pres,sys⟩,?_,?_,?_⟩
  · exact load_value view regions x fin r word mapping imm7 Rn Rt Rt2 hRt hRt2 hRtt binding pay
  · exact ArmCertValue.StepVCore.vholds_of_holds compat rfl holds (load_flags mapping Rt Rt2 imm7 Rn x fin pay)
  · exact PairTail.profile_of_sys pins (EntryBranchPins.sysEq2_symm _ _ sys)

#print axioms ldp_stepV

theorem stp_stepV (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : StoreFacts domain spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (view : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region)
    (r : ArmCertValue.Region) (word : Nat) (binding : Binding view r word mapping imm7 Rn x)
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words)
    (injective : ArmCertValue.Physical.RegionsInjective view regions)
    (vus : List (RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [])
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [] D (StorePay mapping Rt Rt2 imm7 Rn) x fin ∧
      ArmCertValue.Physical.MemVHolds view regions
        [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)] x fin ∧
      ArmCertValue.VHolds vus none x fin ∧ ProfileAt profile fin := by
  obtain ⟨fin,run,packet⟩ := stp_nextG real domain spec config rows mapping m scope image loadBase separated
    base offset budget extra k room page aligned imm7 Rn Rt Rt2 hRn hRt hRt2 x inv profile pins D codeD facts nextPlaced obligations
  obtain ⟨ps,quiet,current,pc,debug,feat,gic,closed,placed,branch,holds,writes,pay,pres,sys⟩ := packet
  refine ⟨fin,run,⟨ps,quiet,current,pc,debug,feat,gic,closed,placed,branch,holds,writes,pay,pres,sys⟩,?_,?_,?_⟩
  · exact store_value view regions x fin r word mapping imm7 Rn Rt Rt2 member fits injective binding pay
  · exact ArmCertValue.StepVCore.vholds_of_holds compat rfl holds (store_flags mapping Rt Rt2 imm7 Rn x fin pay)
  · exact PairTail.profile_of_sys pins (EntryBranchPins.sysEq2_symm _ _ sys)

#print axioms stp_stepV

end NativeAccess.PairSelected
