import DitShim243.SlotMem
import TranslateSpan.SecpDefaultEntry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan HeapV2StepCerts HeapV2StepCerts.C3 ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.SlotCheck

def slotByte (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (a : Nat) : Bool :=
  match mapping (BitVec.ofNat 64 pins.sp) with
  | none => false
  | some n => decide (n ≤ a ∧ a < n + 16)

theorem slotByte_true (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (a : Nat) :
    slotByte pins mapping a = true ↔ RtShim2.ShimMem.slotBytes pins mapping a := by
  cases mapped : mapping (BitVec.ofNat 64 pins.sp) <;>
    simp [slotByte,RtShim2.ShimMem.slotBytes,mapped]

def check (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint) (entry : NativeState) : Bool :=
  let va := BitVec.ofNat 64 pins.sp
  match mapping va with
  | none => false
  | some n => SelectedLoadFacts.checkRAM mapping va && (decide (n + 16 < 2 ^ 56) &&
      ((List.range 16).all (fun i => !(StaticLayout.footprintByte fp (n + i)) && (entry.mem[n + i]?).isSome) &&
      (decide (mapping (plus8 va) = some (n+8)) && SelectedLoadFacts.checkRAM mapping (plus8 va))))

theorem of_check (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint) (entry : NativeState)
    (checked : check pins mapping fp entry = true) :
    RtShim.SlotPrem.ShimSlotStatic pins mapping fp ∧ RtShim.SlotPrem.ShimSlotPresent pins mapping entry := by
  cases mapped : mapping (BitVec.ofNat 64 pins.sp) with
  | none => simp [check,mapped] at checked
  | some n =>
    simp only [check,mapped,Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨ram,bound,bytes,upper,upperRAM⟩ := checked
    obtain ⟨pa,mpa,mmio⟩ := SelectedLoadFacts.ram_of_check mapping (BitVec.ofNat 64 pins.sp) ram
    obtain rfl : n = pa.toNat := Option.some.inj (mapped.symm.trans mpa)
    refine ⟨⟨pa,⟨bound,mpa,mmio,?_,?_⟩⟩,?_⟩
    · intro i hi table
      have each := List.all_eq_true.mp bytes i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at each
      have member := (StaticLayout.footprintByte_true fp (pa.toNat + i)).mpr table
      simp [member] at each
    · intro _
      refine ⟨upper,?_⟩
      obtain ⟨up,mup,noMMIO⟩ := SelectedLoadFacts.ram_of_check mapping (plus8 (BitVec.ofNat 64 pins.sp)) upperRAM
      intro q hq
      have same : q = up := BitVec.eq_of_toNat_eq (Option.some.inj (hq.symm.trans mup))
      rwa [same]
    · intro n hn i hi
      obtain rfl : n = pa.toNat := Option.some.inj (hn.symm.trans mpa)
      have each := List.all_eq_true.mp bytes i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at each
      exact each.2

def checkRegions (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (view : Physical.BytePA) (regions : List (Region × Nat)) : Bool :=
  regions.all fun (r,n) => (List.range n).all fun i =>
    match view r i with
    | none => false
    | some pa => !(slotByte pins mapping pa)

theorem regions_of_check (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (view : Physical.BytePA) (regions : List (Region × Nat))
    (checked : checkRegions pins mapping view regions = true)
    (r : Region) (n : Nat) (member : (r,n) ∈ regions) (i : Nat) (bound : i < n)
    (pa : Nat) (mapped : view r i = some pa) : ¬ RtShim2.ShimMem.slotBytes pins mapping pa := by
  intro inside
  have row := List.all_eq_true.mp checked (r,n) member
  have each := List.all_eq_true.mp row i (List.mem_range.mpr bound)
  have hit := (slotByte_true pins mapping pa).mpr inside
  simp [mapped,hit] at each

#print axioms of_check
#print axioms regions_of_check
end DitShim243.SlotCheck
