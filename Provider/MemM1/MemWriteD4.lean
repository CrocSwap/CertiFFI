import MemM1.MemWriteD3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.MemWriteD4
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

/-- Byte `i` (little-endian) of the stored value. -/
abbrev wbyte {n : Nat} (v : BitVec (n * 8)) (i : Nat) : BitVec 8 :=
  (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * i) 8

/-- The access kind of an `AccDW` access. -/
abbrev akPlain : Access_kind arm_acc_type := AK_explicit { variety := .AV_plain, strength := .AS_normal }

/-- The ONE register fact MemSingle_set reads after TranslateAddress that E17 (ProjRegsEq) does not
    give: `SPESampleInFlight` is false in the state TranslateAddress returns (from any state framed
    from `s`). If it were true, MemSingle_set would run `SPESampleLoadStore`. -/
def SPEKept (a : BitVec 64) (acc : AccessDescriptor) (n : Nat) (s : State) : Prop :=
  ∀ u ad t1, Frame s u → AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 →
    t1.regs.bank_Bool .SPESampleInFlight = false

/-- **Data write under abstract E17.** The actual `Mem_set a n acc v` (STRB: n = 1; STR/STP
    halves: n = 8; any n ∈ {1,2,4,8,16} at an n-aligned VA) for an EL0 NS plain GPR store access
    permitted by `m`, on a state where E17 holds frame-closed, the PA is RAM (not GIC/UART), the
    endianness test reads little-endian, and SPESampleInFlight stays false through translation:
    - Mem_set first only draws choice bookkeeping (state `u`, framed from `s`), then runs the actual
      TranslateAddress (`ad`, `t1`; E17's facts), then appends EXACTLY ONE `memWrite` event;
    - the projected registers are unchanged (`ProjRegsEq s.regs t.regs`);
    - memory: bytes `pa .. pa+n-1` (pa = m.pa a) := the value little-endian; every other byte is
      `t1`'s, i.e. `s`'s except possibly translation-table bytes. -/
theorem memset_E17 (m : ConsumerMap) (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (v : BitVec (n * 8)) (hA : AccDW acc)
    (hE : ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u)
    (hp : m.permitted a acc true (n : Int))
    (hio : NotMMIO (m.pa a)) (hLE : LittleEndian acc s) (hSPE : SPEKept a acc n s) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      Mem_set a n acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite (m.pa a).toNat n (some ad.vaddress.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      ProjRegsEq s.regs t.regs ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + n
        then some (wbyte v (p - (m.pa a).toNat)) else t1.mem[p]?) ∧
      (∀ p, ¬ m.tableByte p → t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + n
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
    ad.fault.statuscode = .Fault_None ∧
    ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
    ad.memattrs.memtype = .MemType_Normal ∧ ProjRegsEq s.regs t1.regs ∧
    ∀ p, ¬ m.tableByte p → t1.mem[p]? = s.mem[p]?
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = m.pa a ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ Q ad t1 := by
    intro u fu
    rcases hE u fu.1 fu.2.1 a acc true (n : Int) hp with ⟨ad, t1, h, hf, hpa, hmt, hr, hm⟩
    rw [fu.1] at hr
    refine ⟨ad, t1, h, hf, by rw [hpa], hSPE u ad t1 fu h, u, fu, h, hf, hpa, hmt, hr, ?_⟩
    intro p hp'
    rw [hm p hp', fu.2.1]
  rcases memset_skel a n hn ha acc s (m.pa a) v hA Q hTA hio hLE with
    ⟨ad, t1, t, ⟨u, fu, h, hf, hpa, hmt, hr, hm⟩, hset, hev, hreg, hmem⟩
  have hak := ak_gpr acc hA.base.gpr hA.exclusive hA.atomicop hA.acqpc hA.acqsc hA.relsc
  have hget : ∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + n
      then some (wbyte v (p - (m.pa a).toNat)) else t1.mem[p]? := by
    intro p
    rw [hmem, wfold_get]
  refine ⟨u, ad, t1, t, fu, h, hf, hpa, hmt, hset, by rw [hev, hak], by rw [hreg]; exact hr, hget, ?_⟩
  intro p hp'
  rw [hget p]
  split
  · rfl
  · exact hm p hp'

/-- Bytes a permitted `n`-byte access at `a` writes are consumer-mapped, so a store that changes
    only them and table bytes keeps `UnmappedSame` (needs `MapOK.contiguous`). -/
theorem unmapped_of (m : ConsumerMap) (hM : MapOK m) (a : BitVec 64) (acc : AccessDescriptor) (n : Nat)
    (hp : m.permitted a acc true (n : Int)) (s t : State) (f : Nat → BitVec 8)
    (hget : ∀ p, ¬ m.tableByte p → t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + n
      then some (f (p - (m.pa a).toNat)) else s.mem[p]?) :
    UnmappedSame m s t := by
  intro p hnm hnt
  show t.mem[p]? = s.mem[p]?
  rw [hget p hnt, if_neg]
  rintro ⟨h1, h2⟩
  apply hnm
  refine ⟨a + BitVec.ofNat 64 (p - (m.pa a).toNat),
    ⟨a, acc, true, (n : Int), p - (m.pa a).toNat, hp, by omega, rfl⟩, ?_⟩
  rw [hM.contiguous a acc true (n : Int) (p - (m.pa a).toNat) hp (by omega)]
  omega

/-- `memset_E17` plus `UnmappedSame m s t` (given `MapOK m`). -/
theorem memset_E17_unmapped (m : ConsumerMap) (hM : MapOK m) (a : BitVec 64) (n : Nat) (hn : SizeOK n)
    (ha : a.toNat % n = 0) (acc : AccessDescriptor) (s : State) (v : BitVec (n * 8)) (hA : AccDW acc)
    (hE : ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u)
    (hp : m.permitted a acc true (n : Int))
    (hio : NotMMIO (m.pa a)) (hLE : LittleEndian acc s) (hSPE : SPEKept a acc n s) :
    ∃ t, Mem_set a n acc v s = .ok () t ∧ ProjRegsEq s.regs t.regs ∧ UnmappedSame m s t ∧
      (∀ i < n, t.mem[(m.pa a).toNat + i]? = some (wbyte v i)) := by
  rcases memset_E17 m a n hn ha acc s v hA hE hp hio hLE hSPE with
    ⟨u, ad, t1, t, fu, h, hf, hpa, hmt, hset, hev, hr, hget, hget'⟩
  refine ⟨t, hset, hr, unmapped_of m hM a acc n hp s t _ hget', ?_⟩
  intro i hi
  rw [hget, if_pos (by omega)]
  simp

/-- **STRB (n = 1) under abstract E17.** -/
theorem strb_E17 (m : ConsumerMap) (a : BitVec 64) (acc : AccessDescriptor) (s : State)
    (v : BitVec (1 * 8)) (hA : AccDW acc)
    (hE : ∀ u : State, u.regs = s.regs → u.mem = s.mem → TranslationAgrees m u)
    (hp : m.permitted a acc true ((1 : Nat) : Int))
    (hio : NotMMIO (m.pa a)) (hLE : LittleEndian acc s) (hSPE : SPEKept a acc 1 s) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true ((1 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧
      ad.paddress = { paspace := .PAS_NonSecure, address := m.pa a } ∧
      ad.memattrs.memtype = .MemType_Normal ∧
      Mem_set a 1 acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite (m.pa a).toNat 1 (some ad.vaddress.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * 1) v)) none) ∧
      ProjRegsEq s.regs t.regs ∧
      (∀ p, t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 1
        then some (wbyte v (p - (m.pa a).toNat)) else t1.mem[p]?) ∧
      (∀ p, ¬ m.tableByte p → t.mem[p]? = if (m.pa a).toNat ≤ p ∧ p < (m.pa a).toNat + 1
        then some (wbyte v (p - (m.pa a).toNat)) else s.mem[p]?) :=
  memset_E17 m a 1 (Or.inl rfl) (Nat.mod_one _) acc s v hA hE hp hio hLE hSPE

/-- **Data write under the STRENGTHENED premise** (what memory's coreVD / agreesKD supply for
    data pages: TranslateAddress keeps ALL registers and ALL memory). Then SPESampleInFlight only
    needs to be false on `s` (Regs20.spe), registers are exactly `s.regs`, and memory is exactly
    `s.mem` with the `n` bytes written: no table-byte exception. -/
theorem memset_strong (a : BitVec 64) (n : Nat) (hn : SizeOK n) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (v : BitVec (n * 8)) (hA : AccDW acc) (pa : BitVec 56)
    (hS : ∀ u : State, u.regs = s.regs → u.mem = s.mem → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs = u.regs ∧ t1.mem = u.mem)
    (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hio : NotMMIO pa) (hLE : LittleEndian acc s) :
    ∃ u ad t1 t, Frame s u ∧ AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      Mem_set a n acc v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat) akPlain
        (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = s.regs ∧
      (∀ p, t.mem[p]? = if pa.toNat ≤ p ∧ p < pa.toNat + n
        then some (wbyte v (p - pa.toNat)) else s.mem[p]?) := by
  let Q : AddressDescriptor → State → Prop := fun ad t1 => ∃ u, Frame s u ∧
    AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧ t1.regs = s.regs ∧ t1.mem = s.mem
  have hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc true (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ Q ad t1 := by
    intro u fu
    rcases hS u fu.1 fu.2.1 with ⟨ad, t1, h, hf, hpa, hr, hm⟩
    have hr' : t1.regs = s.regs := hr.trans fu.1
    refine ⟨ad, t1, h, hf, hpa, by rw [hr']; exact hspe, u, fu, h, hr', hm.trans fu.2.1⟩
  rcases memset_skel a n hn ha acc s pa v hA Q hTA hio hLE with
    ⟨ad, t1, t, ⟨u, fu, h, hr, hm⟩, hset, hev, hreg, hmem⟩
  have hak := ak_gpr acc hA.base.gpr hA.exclusive hA.atomicop hA.acqpc hA.acqsc hA.relsc
  refine ⟨u, ad, t1, t, fu, h, hset, by rw [hev, hak], hreg.trans hr, ?_⟩
  intro p
  rw [hmem, wfold_get, hm]

#print axioms memset_E17
#print axioms unmapped_of
#print axioms memset_E17_unmapped
#print axioms strb_E17
#print axioms memset_strong
end MemM1.MemWriteD4
