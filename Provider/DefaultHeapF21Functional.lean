-- F21 (CertiFFI,): PHYSICAL functional layer for the catalogue provider. No DataBytesLinear /
-- RegionsInjective. Generic lemmas copied verbatim from the sealed d207 release/d207/D207Heap/Functional.lean
-- (agrees_σ0P .. out_store_mem, functional_of_valueP, slotSep_of_walkP); bytePA_OC and shim_functionalP are the
-- catalogue (RunInv) analogues of d207 bytePA_O / functional_heapv2P.
import DefaultHeapValueRunP
import DefaultHeapFunctional
import DefaultHeapF21Leaf
import ArmCertValue.PhysicalGlue
import ArmCertValue.Bridges
import TranslateSpan.Heap
import HP1Int.FunctionalWalk
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.HeapV2PlanP
open ArmCertValue ArmCertValue.HeapV2Plan CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General

/-! ## Physical run -/

theorem agrees_σ0P (bytePA : Physical.BytePA) (s : St) (bytes : Nat → BitVec 8)
    (hI : ∀ j, j < 32 → Physical.regionByte bytePA s I j = some (bytes j)) :
    Physical.Agrees bytePA (mkInputs s bytes) σ0 s := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    cases r with
    | x k =>
      simp only [σ0, Option.some.injEq] at h
      subst h
      rw [mkInputs_getD s bytes _ (by omega)]
      simp only [inputVal, if_neg (show ¬ 32 + k.val < 32 by omega), dif_pos (show 32 + k.val < 63 by omega)]
      congr 2
      exact Fin.ext (by simp)
    | sp =>
      simp only [σ0, Option.some.injEq] at h
      subst h
      rw [mkInputs_getD s bytes _ (by omega)]
      simp [inputVal]
  · intro n z c v h
    simp only [σ0, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mkInputs_getD s bytes _ (by omega)] <;> simp [inputVal]
  · intro g j i k h
    simp only [σ0] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2; subst h1
      obtain ⟨rfl, hj⟩ := hc
      rw [hI j hj, mkInputs_getD s bytes j (by omega)]
      simp only [inputVal, if_pos hj, Nat.mul_zero, BitVec.ushiftRight_zero]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (bytes j).isLt
      omega
    · cases h

/-- **H-P1 on the run, physical.** As the sealed hp1_run, over a physical byte view; no RegionCoherent premise. -/
theorem hp1_runP (bytePA : Physical.BytePA) (run : Nat → St)
    (inputs : List (BitVec 64)) (hlen : inputs.length = 68) (hbytes : ∀ i, i < 32 → (inputs.getD i 0).toNat < 256)
    (hA0 : Physical.Agrees bytePA inputs σ0 (run 0))
    (hplan : Physical.PlanHolds bytePA regions run 0 plan) :
    ∀ j, j < 32 → Physical.regionByte bytePA (run 357) O j =
      some (BitVec.ofNat 8 ((TranslateValue.HP1.inVal inputs ^ 2 % TranslateValue.HP1.p256k1) / 256 ^ j)) := by
  obtain ⟨σf, hc⟩ : ∃ σf, compileRun regions σ0 68 plan = some (D, σf) := by
    have h := compiles_D
    cases hr : compileRun regions σ0 68 plan with
    | none => rw [hr] at h; cases h
    | some p =>
      obtain ⟨d, σf⟩ := p
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨σf, rfl⟩
  have hB0 : σ0.Bounded inputs.length := by rw [hlen]; exact σ0_bounded
  have hrun := Physical.run_agrees bytePA regions run plan 0 inputs σ0 σf D hA0 hB0 hplan (by rw [hlen]; exact hc)
  rw [plan_length, Nat.zero_add] at hrun
  have hout := outs_tracked
  rw [hc] at hout
  simp only [Option.map_some, Option.some.injEq] at hout
  intro j hj
  have hm : σf.memB O j = some (outs.getD j (0, 0)) := by
    have := congrArg (fun l => l[j]?) hout
    simpa [List.getElem?_map, List.getElem?_range hj] using this
  have hm' : σf.memB O j = some ((outs.getD j (0, 0)).1, (outs.getD j (0, 0)).2) := by
    rw [hm]
  rw [hrun.1.2.2 O j (outs.getD j (0, 0)).1 (outs.getD j (0, 0)).2 hm']
  exact congrArg some (TranslateValue.HP1.hp1_bytes inputs hlen hbytes j hj)


/-! ## Input / output bridges for the anchored view -/

theorem dataVA_in (p : HeapV2E17.Pins) (j : Nat) :
    HeapV2E17.dataVA p (18 + 4 * j, 2, (j : Int), 1, false) = BitVec.ofNat 64 (p.x1 + j) := by
  apply BitVec.eq_of_toNat_eq
  simp [HeapV2E17.dataVA, HeapV2E17.pin, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem dataVA_out (p : HeapV2E17.Pins) (j : Nat) :
    HeapV2E17.dataVA p (153 + 3 * j, 1, (j : Int), 1, true) = BitVec.ofNat 64 (p.x0 + j) := by
  apply BitVec.eq_of_toNat_eq
  simp [HeapV2E17.dataVA, HeapV2E17.pin, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem anchorSite_I (j : Nat) : TranslateHeapSpan.anchorSite (I, j) = (18 + 4 * j, 2, (j : Int), 1, false) := by
  simp [TranslateHeapSpan.anchorSite]

theorem bytePA_I (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (j : Nat) :
    TranslateHeapSpan.bytePA p mapping I j = mapping (BitVec.ofNat 64 (p.x1 + j)) := by
  unfold TranslateHeapSpan.bytePA TranslateSpan.anchoredView TranslateHeapSpan.anchor
  rw [anchorSite_I, dataVA_in]
  simp [TranslateHeapSpan.delta]

theorem regionByte_IP (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (s : St) (j : Nat) :
    Physical.regionByte (TranslateHeapSpan.bytePA p mapping) s I j = Release.bufByte mapping s p.x1 j := by
  unfold Physical.regionByte Release.bufByte
  rw [bytePA_I]

/-- Every output byte has its own actual one-byte store (153+3j, x0, j). -/
theorem out_stores : (List.range 32).all (fun j =>
    ArmCert.Translate.Model.HeapV2Plan.symbolicAccesses.contains (153 + 3 * j, 1, (j : Int), 1, true)) = true := by
  decide

theorem out_store_mem (j : Nat) (hj : j < 32) :
    (153 + 3 * j, 1, (j : Int), 1, true) ∈ ArmCert.Translate.Model.HeapV2Plan.symbolicAccesses :=
  List.mem_of_elem_eq_true (List.all_eq_true.1 out_stores j (List.mem_range.2 hj))

/-- **Output bridge (option B).** At any E17 body state, the anchored physical byte of O j (pair-store anchor +
    in-page offset) is the translation of the actual byte store's start x0 + j. -/
theorem functional_of_valueP (real : Type) [Sail.SailReal real] (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (e : NativeState) (Inv : Nat → NativeState → Prop)
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real (stateAt real e 7) k))
    (hsteps : ∀ k (h : k < plan.length),
      Physical.StepFact real Inv (TranslateHeapSpan.bytePA pins mapping) regions plan k h)
    (hO : ∀ j, j < 32 → TranslateHeapSpan.bytePA pins mapping O j = mapping (BitVec.ofNat 64 (pins.x0 + j)))
    (bytes : Nat → BitVec 8)
    (hI : ∀ j, j < 32 → Physical.regionByte (TranslateHeapSpan.bytePA pins mapping) (stateAt real e 7) I j = some (bytes j))
    (hIe : ∀ j, j < 32 → Release.bufByte mapping e pins.x1 j = some (bytes j))
    (hOut : ∀ i, i < 32 → Release.bufByte mapping (stateAt real e 369) pins.x0 i =
      Release.bufByte mapping (stateAt real e 364) pins.x0 i)
    (hx0 : (stateAt real e 369).regs.gpr[0] = 0#64) :
    Release.Functional mapping pins e (stateAt real e 369) := by
  have hplan := Physical.planHolds_of_steps real Inv (TranslateHeapSpan.bytePA pins mapping) regions plan
    (stateAt real e 7) hinv hsteps
  have hA0 := agrees_σ0P (TranslateHeapSpan.bytePA pins mapping) (stateAt real e 7) bytes hI
  have h := hp1_runP (TranslateHeapSpan.bytePA pins mapping) (stateAt real (stateAt real e 7))
    (mkInputs (stateAt real e 7) bytes) (mkInputs_length _ _) (mkInputs_bytes _ _) hA0 hplan
  have hval := inVal_mkInputs mapping pins (stateAt real e 7) e bytes hIe
  refine ⟨hx0, ?_⟩
  intro i hi
  have hb : Release.bufByte mapping (stateAt real (stateAt real e 7) 357) pins.x0 i =
      Physical.regionByte (TranslateHeapSpan.bytePA pins mapping) (stateAt real (stateAt real e 7) 357) O i := by
    unfold Physical.regionByte Release.bufByte
    rw [hO i hi]
  rw [hOut i hi, show (364 : Nat) = 7 + 357 from rfl, Release.body_index, hb, h i hi, hval, p256k1_eq]



theorem slotSep_of_walkP (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (hd : TranslateMem.RegionsDisjoint p)
    (hsp : p.sp % 16 = 0)
    (walk : TranslateMem.AccessLeaf p mapping) (slot : TranslateMem.SlotLeaf p mapping) (nd : TranslateMem.NoDoubleMapSlot p mapping)
    (slotDisj : p.x1 + 32 ≤ p.sp ∨ p.sp + 16 ≤ p.x1) (spHi : p.sp + 16 ≤ 2 ^ 64) :
    ∀ j, j < 32 → ∀ q, mapping (BitVec.ofNat 64 (p.x1 + j)) = some q → ¬ TranslateMem.SlotBytes p mapping q := by
  intro j hj q hq ⟨n, hn, lo, hi⟩
  obtain ⟨b0, b1, b2, b3, d1, d2, d3⟩ := hd
  have mem : (I, j) ∈ ArmCertValue.HeapV2Mem.heapv2Bytes :=
    TranslateHeapSpan.tracked_of_bound I j (by decide) (by simp [I]; omega)
  have he := TranslateHeapSpan.anchor_accessed (I, j) mem
  rw [anchorSite_I] at he
  obtain ⟨l, hl⟩ := walk _ he
  rw [dataVA_in] at hl
  rw [hq] at hl; cases hl
  have oq := TranslateMem.leafPA_mod (BitVec.ofNat 64 (p.x1 + j)) l
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.x1 + j < 2 ^ 64 by omega)] at oq
  obtain ⟨l', hl'⟩ := slot
  have en : n = TranslateMem.leafPA (BitVec.ofNat 64 p.sp) l' := by rw [hn] at hl'; exact Option.some.inj hl'
  have on := TranslateMem.leafPA_mod (BitVec.ofNat 64 p.sp) l'
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.sp < 2 ^ 64 by omega), ← en] at on
  have sameFrame : TranslateMem.leafPA (BitVec.ofNat 64 (p.x1 + j)) l / 4096 = n / 4096 := by
    have := Nat.div_add_mod (TranslateMem.leafPA (BitVec.ofNat 64 (p.x1 + j)) l) 4096
    have := Nat.div_add_mod n 4096
    have : p.sp % 4096 + 16 ≤ 4096 := by omega
    omega
  have page := nd j hj _ n hq hn sameFrame
  have := Nat.div_add_mod (p.x1 + j) 4096; have := Nat.div_add_mod p.sp 4096
  have := Nat.div_add_mod (TranslateMem.leafPA (BitVec.ofNat 64 (p.x1 + j)) l) 4096; have := Nat.div_add_mod n 4096
  omega



/-- Output bridge (option B) at any catalogue body state: d207 bytePA_O with the provider RunInv. -/
theorem bytePA_OC {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64}
    {pins : HeapV2E17.Pins} {entry : NativeState} {budget k : Nat} {catalogue : NativeMteTagCheck.ControlCatalogue}
    {capacity : Nat} {drawsBefore : Nat → Nat} {x : NativeState}
    (inv : ReleaseProfile.DefaultHeapRun.RunInv spec config rows mapping base pins entry budget k catalogue capacity
      drawsBefore x) (hd : TranslateMem.RegionsDisjoint pins)
    (aligned : pins.sp % 16 = 0 ∧ pins.x0 % 16 = 0 ∧ pins.x1 % 16 = 0) (j : Nat) (hj : j < 32) :
    TranslateHeapSpan.bytePA pins mapping O j = mapping (BitVec.ofNat 64 (pins.x0 + j)) := by
  have span := TranslateHeapSpan.span_compatible inv.1.body.core.closed inv.1.body.core.v1.current.images.topology hd
    aligned _ (out_store_mem j hj) 0 Nat.zero_lt_one
  have hloc : TranslateHeapSpan.accessLoc (153 + 3 * j, 1, (j : Int), 1, true) = (O, j) := by
    simp [TranslateHeapSpan.accessLoc, O]
  rw [hloc, Nat.add_zero, dataVA_out] at span
  rw [span]
  cases mapping (BitVec.ofNat 64 (pins.x0 + j)) <;> rfl

end ArmCertValue.HeapV2PlanP

namespace ReleaseProfile.DefaultHeapRunP
open ReleaseProfile.DefaultHeapRun
open ArmCertValue ArmCertValue.HeapV2Plan CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.CruxGenGuarded HeapV2StepCerts

/-- Physical analogue of the provider's shim_functional: (dbl, inj) replaced by (hd, nd). -/
theorem shim_functionalP (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real entry 7) budget catalogue capacity drawsBefore)
    (hb : 357 ≤ budget)
    (hd : TranslateMem.RegionsDisjoint pins) (nd : TranslateMem.NoDoubleMapPA pins mapping)
    (inputFrame : ∀ i, i < 32 → Release.bufByte mapping (stateAt real entry 7) pins.x1 i =
      Release.bufByte mapping entry pins.x1 i)
    (outputFrame : ∀ i, i < 32 → Release.bufByte mapping (stateAt real entry 369) pins.x0 i =
      Release.bufByte mapping (stateAt real entry 364) pins.x0 i)
    (x0Frame : (stateAt real entry 369).regs.gpr[0] = (stateAt real entry 364).regs.gpr[0]) :
    Release.Functional mapping pins entry (stateAt real entry 369) := by
  let bodyEntry := stateAt real entry 7
  let bytes : Nat → BitVec 8 := fun i => (Release.bufByte mapping entry pins.x1 i).getD 0#8
  have present := input_present catalogue capacity drawsBefore dp
  have bodyBytes : ∀ i, i < 32 →
      Release.bufByte mapping bodyEntry pins.x1 i = some (bytes i) := by
    intro i hi
    obtain ⟨b, h⟩ := present i hi
    have he := (inputFrame i hi).symm.trans h
    simp only [bytes, he, Option.getD_some]
    exact h
  have entryBytes : ∀ i, i < 32 → Release.bufByte mapping entry pins.x1 i = some (bytes i) := by
    intro i hi
    rw [← inputFrame i hi]
    exact bodyBytes i hi
  have hI : ∀ i, i < 32 →
      Physical.regionByte (TranslateHeapSpan.bytePA pins mapping) bodyEntry I i = some (bytes i) := by
    intro i hi
    rw [ArmCertValue.HeapV2PlanP.regionByte_IP]
    exact bodyBytes i hi
  have hinv : ∀ k, k < plan.length →
      RunInv spec config rows mapping base pins bodyEntry budget k catalogue capacity drawsBefore (stateAt real bodyEntry k) := by
    intro k hk
    rw [plan_length] at hk
    exact prefixes real spec config rows mapping base pins bodyEntry budget catalogue capacity drawsBefore dp hb k (by omega)
  have inv := prefixes real spec config rows mapping base pins bodyEntry budget catalogue capacity drawsBefore dp hb 357 (by decide)
  have zero : (stateAt real entry 364).regs.gpr[0] = 0#64 := by
    rw [show (364 : Nat) = 7 + 357 from rfl, Release.body_index]
    simpa [bodyEntry, RegBind.regVal, Fin.castLE] using ValBind.scrub_at_357 inv.1.valBind ⟨0, by decide⟩
  have aligned : pins.sp % 16 = 0 ∧ pins.x0 % 16 = 0 ∧ pins.x1 % 16 = 0 :=
    ⟨dp.pinAligned 0, dp.pinAligned 1, dp.pinAligned 2⟩
  exact ArmCertValue.HeapV2PlanP.functional_of_valueP real mapping pins entry
    ((fun k => RunInv spec config rows mapping base pins bodyEntry budget k catalogue capacity drawsBefore)) hinv
    (ReleaseProfile.DefaultHeapRunP.value_steps real spec config rows mapping base pins bodyEntry budget catalogue capacity
      drawsBefore dp hb hd nd)
    (fun j hj => ArmCertValue.HeapV2PlanP.bytePA_OC inv hd aligned j hj)
    bytes hI entryBytes outputFrame (x0Frame.trans zero)

end ReleaseProfile.DefaultHeapRunP

#print axioms ArmCertValue.HeapV2PlanP.functional_of_valueP
#print axioms ArmCertValue.HeapV2PlanP.slotSep_of_walkP
#print axioms ReleaseProfile.DefaultHeapRunP.shim_functionalP
