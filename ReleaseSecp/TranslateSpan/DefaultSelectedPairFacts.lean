import TranslateSpan.DefaultFiniteMem
import TranslateSpan.DefaultPairSelected
import TranslateSpan.SelectedStoreFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertValue ArmCertMemPipe HeapV2StepCerts NativeAccess NativeAccess.LdpBytes
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.DefaultSelectedPairFacts
open TranslateSpan.SelectedLoadFacts TranslateSpan.SelectedStoreFacts PairGeometry

theorem load_facts (domain : BitVec 64 → Prop) (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop) (sites : List SelectedMap.Site) (code : List (BitVec 64))
    (site : SelectedMap.Site) (member : site ∈ sites) (read : site.write = false)
    (view : Physical.BytePA) (r : Region) (word : Nat)
    (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState)
    (source : LdpBytes.pairAddr x Rn imm7 = site.address)
    (span : SelectedBinding.At view r word mapping site.address)
    (targets : Targets domain mapping site.address)
    (data : BitVec 128)
    (payload : ∀ i, i < 16 → Physical.regionByte view x r (8 * word + i) = some (data.extractLsb' (8 * i) 8)) :
    DefaultPairSelected.LoadFacts domain mapping (SelectedMap.consumerMap sites code mapping table) imm7 Rn x := by
  unfold DefaultPairSelected.LoadFacts DefaultPairSelected.LoadOneData DefaultPairSelected.LoadSplitData DefaultPairSelected.LoadByteData
  rw [source]
  unfold SelectedBinding.At at span
  unfold Targets at targets
  generalize chosen : PairGeometry.selected site.address = c at span targets ⊢
  cases c with
  | one16 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    refine ⟨pa,data,mapped,mmio,?_,?_⟩
    · intro i hi
      have h := payload i hi
      rw [Physical.regionByte,span pa.toNat mapped i hi,Option.bind_some] at h
      exact h
    · intro acc shape
      have hs : DataShape site.write acc := by
        rw [read]
        exact shape
      exact SelectedMap.one_member sites code mapping table site member chosen acc hs
  | two8 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    refine ⟨pa,data,mapped,mmio,?_,?_⟩
    · intro j i hi
      have h := payload (8 * j.val + i) (by omega)
      have lin := span j (pa j).toNat (mapped j) i hi
      rw [show 8 * word + (8 * j.val + i) = 8 * word + 8 * j.val + i by omega,
        Physical.regionByte,lin,Option.bind_some] at h
      rw [DefaultPairValue.halfValue_byte data j i hi]
      exact h
    · intro acc shape j
      have hs : DataShape site.write acc := by
        rw [read]
        exact shape
      exact SelectedMap.half_member sites code mapping table site member chosen j acc hs
  | bytes =>
    obtain ⟨domains,pa,mapped,mmio⟩ := targets
    refine ⟨domains,pa,data,mapped,mmio,?_,?_⟩
    · intro j
      have h := payload j.val j.isLt
      rw [Physical.regionByte,span j (pa j).toNat (mapped j),Option.bind_some] at h
      exact h
    · intro acc shape j aligned
      have hs : DataShape site.write acc := by
        rw [read]
        exact shape
      have h := SelectedMap.byte_member sites code mapping table site member chosen j acc hs aligned
      simpa [BitVec.addInt] using h


#print axioms load_facts

theorem store_facts (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (mapping : BitVec 64 → Option Nat) (table D : Nat → Prop)
    (sites : List SelectedMap.Site) (code : List (BitVec 64))
    (site : SelectedMap.Site) (member : site ∈ sites) (write : site.write = true)
    (view : Physical.BytePA) (r : Region) (word : Nat)
    (imm7 : BitVec 7) (Rn : BitVec 5) (x : NativeState)
    (source : LdpBytes.pairAddr x Rn imm7 = site.address)
    (span : SelectedBinding.At view r word mapping site.address)
    (targets : SelectedLoadFacts.Targets domain mapping site.address)
    (output : OutputSafe spec view r word D) :
    DefaultPairSelected.StoreFacts domain spec mapping (SelectedMap.consumerMap sites code mapping table) D imm7 Rn x := by
  unfold DefaultPairSelected.StoreFacts DefaultPairSelected.StoreOneData DefaultPairSelected.StoreSplitData DefaultPairSelected.StoreByteData
  rw [source]
  unfold SelectedBinding.At at span
  unfold SelectedLoadFacts.Targets at targets
  generalize chosen : PairGeometry.selected site.address = c at span targets ⊢
  cases c with
  | one16 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    refine ⟨pa,mapped,mmio,?_,?_,?_⟩
    · intro i hi
      exact (output i hi _ (span pa.toNat mapped i hi)).1
    · intro i hi
      exact (output i hi _ (span pa.toNat mapped i hi)).2
    · intro acc shape
      have hs : DataShape site.write acc := by
        rw [write]
        exact shape
      exact SelectedMap.one_member sites code mapping table site member chosen acc hs
  | two8 =>
    obtain ⟨pa,mapped,mmio⟩ := targets
    have safe (j : Fin 2) (i : Nat) (hi : i < 8) :=
      output (8 * j.val + i) (by omega) ((pa j).toNat + i)
        (by simpa only [Nat.add_assoc] using span j (pa j).toNat (mapped j) i hi)
    refine ⟨pa,mapped,mmio,?_,?_,?_⟩
    · intro j i hi; exact (safe j i hi).1
    · intro j i hi; exact (safe j i hi).2
    · intro acc shape j
      have hs : DataShape site.write acc := by
        rw [write]
        exact shape
      exact SelectedMap.half_member sites code mapping table site member chosen j acc hs
  | bytes =>
    obtain ⟨domains,pa,mapped,mmio⟩ := targets
    refine ⟨domains,pa,mapped,mmio,?_,?_,?_⟩
    · intro j; exact (output j.val j.isLt _ (span j (pa j).toNat (mapped j))).1
    · intro j; exact (output j.val j.isLt _ (span j (pa j).toNat (mapped j))).2
    · intro acc shape j aligned
      have hs : DataShape site.write acc := by
        rw [write]
        exact shape
      have h := SelectedMap.byte_member sites code mapping table site member chosen j acc hs aligned
      simpa [BitVec.addInt] using h


#print axioms store_facts

theorem ldp_step (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (language : ArmCertPipe.ValuePlan.Language) (plan : List (ArmCertPipe.ValuePlan.Step language))
    (profile : AccessProfile) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (capacity : Nat) (drawsBefore : Nat → Nat) (x : NativeState)
    (inv : DefaultMTE2.Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (statusRoom : drawsBefore k < capacity)
    (statusBound : drawsBefore k + DefaultBudget.cost (pairAddr x Rn imm7) ≤ capacity)
    (drawBound : drawsBefore k + DefaultBudget.cost (pairAddr x Rn imm7) ≤ drawsBefore (k + 1))
    (roomPlan : k < plan.length)
    (compiles : (ArmCertPipe.ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (D : Nat → Prop) (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : DefaultPairSelected.LoadFacts domain mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (r : Region) (word : Nat) (binding : DefaultPairSelected.Binding view r word mapping imm7 Rn x)
    (vus : List (RegBind.Reg × Option VUpd))
    (compat : StepVCore.Compat vus [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)])
    (planEntry : plan[k] = ArmCertPipe.ValuePlan.legacy language ⟨vus,none,
      [.load (.x (RegBind.rk Rt)) r word,.load (.x (RegBind.rk Rt2)) r (word + 1)]⟩)
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultMTE2.Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
        language view regions σ0 inputs plan entry capacity drawsBefore (k + 1) fin ∧
      ArmCertPipe.ValuePlan.Holds language view regions plan[k] x fin ∧ CurrentMTE2.BodyFrame D x fin := by
  have effectOf (fin : NativeState) (holds : RegBind.Holds [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] x fin)
      (pay : DefaultPairSelected.LoadPay mapping Rt Rt2 imm7 Rn x fin) :
      ArmCertPipe.ValuePlan.Holds language view regions plan[k] x fin := by
    rw [planEntry]
    apply (ArmCertPipe.ValuePlan.holds_legacy language view regions _ x fin).mpr
    exact ⟨StepVCore.vholds_of_holds compat rfl holds
      (DefaultPairSelected.load_flags mapping Rt Rt2 imm7 Rn x fin pay),
      DefaultPairSelected.load_value view regions x fin r word mapping imm7 Rn Rt Rt2
        hRt hRt2 hRtt binding pay⟩
  obtain ⟨fin,run,after,effect,frame⟩ := DefaultMTE2.mem_next_finite real inv statusRoom statusBound drawBound room roomPlan compiles page aligned separated
    (fun _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real domain spec config rows mapping m imm7 Rn Rt Rt2 hRn hRt hRt2
      hRtt x profile inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts domain mapping m imm7 Rn g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping Rt Rt2 imm7 Rn g sp mm nz pay)
    rfl nextPlaced obligations effectOf
  exact ⟨fin,run,after,effect,⟨frame.writes.mono (fun _ h => h.elim),frame.z,frame.tls⟩⟩


#print axioms ldp_step

theorem stp_step (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (view : Physical.BytePA) (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64))
    (language : ArmCertPipe.ValuePlan.Language) (plan : List (ArmCertPipe.ValuePlan.Step language))
    (profile : AccessProfile) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (capacity : Nat) (drawsBefore : Nat → Nat) (x : NativeState)
    (inv : DefaultMTE2.Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue language view regions σ0 inputs plan entry capacity drawsBefore k x)
    (statusRoom : drawsBefore k < capacity)
    (statusBound : drawsBefore k + DefaultBudget.cost (pairAddr x Rn imm7) ≤ capacity)
    (drawBound : drawsBefore k + DefaultBudget.cost (pairAddr x Rn imm7) ≤ drawsBefore (k + 1))
    (roomPlan : k < plan.length)
    (compiles : (ArmCertPipe.ValuePlan.compileRun language regions σ0 inputs.length plan).isSome = true)
    (D : Nat → Prop) (tableD : Separated (rowsFootprint spec.imageRows).byte D)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : DefaultPairSelected.StoreFacts domain spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (r : Region) (word : Nat) (binding : DefaultPairSelected.Binding view r word mapping imm7 Rn x)
    (member : r ∈ regions) (fits : 8 * word + 16 ≤ 8 * r.words)
    (injective : Physical.RegionsInjective view regions)
    (vus : List (RegBind.Reg × Option VUpd))
    (compat : StepVCore.Compat vus [])
    (planEntry : plan[k] = ArmCertPipe.ValuePlan.legacy language ⟨vus,none,
      [.store (.x (RegBind.rk Rt)) r word,.store (.x (RegBind.rk Rt2)) r (word + 1)]⟩)
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultMTE2.Inv spec config rows mapping m scope image loadBase base offset budget profile catalogue
        language view regions σ0 inputs plan entry capacity drawsBefore (k + 1) fin ∧
      ArmCertPipe.ValuePlan.Holds language view regions plan[k] x fin ∧ CurrentMTE2.BodyFrame D x fin := by
  have effectOf (fin : NativeState) (holds : RegBind.Holds [] x fin)
      (pay : DefaultPairSelected.StorePay mapping Rt Rt2 imm7 Rn x fin) :
      ArmCertPipe.ValuePlan.Holds language view regions plan[k] x fin := by
    rw [planEntry]
    apply (ArmCertPipe.ValuePlan.holds_legacy language view regions _ x fin).mpr
    exact ⟨StepVCore.vholds_of_holds compat rfl holds
      (DefaultPairSelected.store_flags mapping Rt Rt2 imm7 Rn x fin pay),
      DefaultPairSelected.store_value view regions x fin r word mapping imm7 Rn Rt Rt2
        member fits injective binding pay⟩
  obtain ⟨fin,run,after,effect,frame⟩ := DefaultMTE2.mem_next_finite real inv statusRoom statusBound drawBound room roomPlan compiles page aligned separated
    tableD codeD
    (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real domain spec config rows mapping m imm7 Rn Rt Rt2 hRn hRt hRt2
      D x profile inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts domain spec mapping m D imm7 Rn g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping Rt Rt2 imm7 Rn g sp mm nz pay)
    rfl nextPlaced obligations effectOf
  exact ⟨fin,run,after,effect,frame⟩


#print axioms stp_step

end TranslateSpan.DefaultSelectedPairFacts
