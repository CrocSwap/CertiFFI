import MemM1.MemReadIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemWriteD1
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.MemReadIF

/-! ### Data-write helpers: alignment for sizes 1,2,4,8,16; the RAM byte writes; PhysMemWrite. -/

/-- Access sizes MemSingle_set accepts. -/
def SizeOK (n : Nat) : Prop := n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16

theorem align_gen (x : BitVec 64) (y : Nat) (hy : SizeOK y) :
    Align_bits x (y : Int) = BitVec.ofNat 64 (x.toNat / y * y) := by
  unfold Align_bits Align_int fdiv_int Slice_int get_slice_int
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.castWidth_eq, Sail.BitVec.toNatInt]
  have hlt := x.isLt
  split
  · next h => exact absurd (of_decide_eq_true h.1) (by simp)
  split
  · next h => omega
  rw [show (BitVec.length x + 1) = 65 from rfl]
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> omega

theorem align16 (x : BitVec 64) : Align_bits x (16 : Int) = BitVec.ofNat 64 (x.toNat / 16 * 16) :=
  align_gen x 16 (by unfold SizeOK; omega)

theorem isAligned_gen (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0) :
    IsAligned__1 a (n : Int) = true := by
  have h := align_gen a n hn
  unfold IsAligned__1
  rw [h]
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have hlt := a.isLt
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem allIn_gen (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0) (s : State) :
    AllInAlignedQuantity a (n : Int) 16 s = .ok true s := by
  have h : Align_bits (BitVec.subInt (BitVec.addInt a (n : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a (n : Int)) 1).toNat / 16 * 16) := align16 _
  have h' := align16 a
  have hle : ((n : Int) ≤b 16) = true := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  unfold AllInAlignedQuantity
  simp only [ArmFull.assert, PreSail.assert, h, h', hle, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, ↓reduceIte]
  have hlt := a.isLt
  have e : (BitVec.subInt (BitVec.addInt a (n : Int)) 1).toNat = a.toNat + n - 1 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    · simp [BitVec.subInt, BitVec.addInt, BitVec.toNat_add, BitVec.toNat_sub]
      omega
  rw [e]
  have e2 : (a.toNat + n - 1) / 16 * 16 = a.toNat / 16 * 16 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  rw [e2]
  simp

/-! ### RAM byte writes. -/

/-- The memory after writing `g 0, ..., g (n-1)` at `addr, ..., addr + n - 1`, as `writeBytes`
    builds it (a left fold of `insert`s). -/
def wfold (m : Std.ExtHashMap Nat (BitVec 8)) (addr n : Nat) (g : Nat → BitVec 8) :
    Std.ExtHashMap Nat (BitVec 8) :=
  (List.ofFn (fun i : Fin n => (addr + i.val, g i.val))).foldl (fun m q => m.insert q.1 q.2) m

theorem wfold_get (m : Std.ExtHashMap Nat (BitVec 8)) (addr n : Nat) (g : Nat → BitVec 8) (p : Nat) :
    (wfold m addr n g)[p]? = if addr ≤ p ∧ p < addr + n then some (g (p - addr)) else m[p]? := by
  induction n with
  | zero =>
    unfold wfold
    simp only [List.ofFn_zero, List.foldl_nil]
    rw [if_neg (by omega)]
  | succ n ih =>
    unfold wfold at ih ⊢
    rw [List.ofFn_succ_last]
    erw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [Std.ExtHashMap.getElem?_insert, ih]
    by_cases hp : addr + n = p
    · subst hp
      simp
    · have : (addr + n == p) = false := by simpa using hp
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hq : addr ≤ p ∧ p < addr + n
      · rw [if_pos hq, if_pos (by omega)]
      · rw [if_neg hq, if_neg (by omega)]

theorem forM_write (L : List (Nat × BitVec 8)) (u : State) :
    (List.forM L (fun (x : Nat × BitVec 8) => match x with | (a, v) => PreSail.writeByte a v) :
      SailM PUnit) u = .ok ⟨⟩ { u with mem := L.foldl (fun m q => m.insert q.1 q.2) u.mem } := by
  induction L generalizing u with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.forM_cons, List.foldl_cons]
    show EStateM.bind (PreSail.writeByte a b) (fun _ => List.forM tl _) u = _
    have hw : (PreSail.writeByte a b : SailM PUnit) u = .ok ⟨⟩ { u with mem := u.mem.insert a b } := rfl
    simp only [EStateM.bind, hw]
    exact ih _

theorem writeBytes_eq {n : Nat} (addr : Nat) (v : BitVec (8 * n)) (u : State) :
    (PreSail.writeBytes addr v : SailM Bool) u =
      .ok true { u with mem := wfold u.mem addr n (fun j => v.extractLsb' (8 * j) 8) } := by
  unfold PreSail.writeBytes
  show EStateM.bind (List.forM _ _) (fun _ => pure true) u = _
  simp only [EStateM.bind, forM_write]
  rfl

/-- The access kind of an EL0 plain GPR access (not exclusive / atomic / acquire / release). -/
theorem ak_gpr (acc : AccessDescriptor) (h1 : acc.acctype = .AccessType_GPR)
    (h2 : acc.exclusive = false) (h3 : acc.atomicop = false) (h4 : acc.acqpc = false)
    (h5 : acc.acqsc = false) (h6 : acc.relsc = false) :
    AccessDescriptor_to_Access_kind acc =
      AK_explicit { variety := .AV_plain, strength := .AS_normal } := by
  unfold AccessDescriptor_to_Access_kind
  rw [h1]
  simp [h2, h3, h4, h5, h6]

/-- `PhysMemWrite` of `n` RAM bytes (not GIC/UART): one `memWrite` event (value `some data`, tag
    `none`), then the bytes little-endian at `pa, ..., pa + n - 1`. -/
theorem physWrite (ad : AddressDescriptor) (n : Nat) (acc : AccessDescriptor) (u : State)
    (data : BitVec (8 * n)) (hio : NotMMIO ad.paddress.address) :
    PhysMemWrite ad n acc none data u =
      .ok (CreatePhysMemRetStatus .Fault_None)
        { u with
          events := u.events.push (.memWrite ad.paddress.address.toNat n (some ad.vaddress.toNat)
            (AccessDescriptor_to_Access_kind acc) (some data) none)
          mem := wfold u.mem ad.paddress.address.toNat n (fun j => data.extractLsb' (8 * j) 8) } := by
  have g : (Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb ad.paddress.address
      (Sail.Int.toNatChecked ((Sail.BitVec.length ad.paddress.address : Int) -i 1)) 16) ==
      Sail.BitVec.castWidth (m := 40) (ZeroExtend1 (m := Sail.Int.toNatChecked (((56 -i 1) -i 16) +i 1))
        GIC_BASE)) = false := by
    simp only [Sail.BitVec.castWidth_eq, beq_eq_false_iff_ne]
    exact hio.1
  have ua : (Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb ad.paddress.address
      (Sail.Int.toNatChecked ((Sail.BitVec.length ad.paddress.address : Int) -i 1)) 16) ==
      Sail.BitVec.castWidth (m := 40) (ZeroExtend1 (m := Sail.Int.toNatChecked (((56 -i 1) -i 16) +i 1))
        UART_BASE)) = false := by
    simp only [Sail.BitVec.castWidth_eq, beq_eq_false_iff_ne]
    exact hio.2
  unfold PhysMemWrite
  simp only [g, ua, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, ArmFull.ConcurrencyInterfaceV1.sail_mem_write, PreSail.sail_mem_write,
    PreSail.logEvent, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, write_request,
    Sail.BitVec.castWidth_eq]
  rw [writeBytes_eq]
  rfl

#print axioms align_gen
#print axioms isAligned_gen
#print axioms allIn_gen
#print axioms wfold_get
#print axioms writeBytes_eq
#print axioms ak_gpr
#print axioms physWrite
end MemM1.MemWriteD1
