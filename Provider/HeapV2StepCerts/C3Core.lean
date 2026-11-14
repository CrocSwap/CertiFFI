-- Memory (certiffi (c3)): generic premise derivation for the heap-v2 memory steps: plan VA from
-- RegBind, per-descriptor access data from closed membership (DataShape), static data checks,
-- and loaded-byte values from DataPresent.
import HeapV2StepCerts.RegBind
import ArmCertTranslateModel.C9Checks
import ArmCertTranslateModel.ClosedTable
import ArmCertWalk.MemPair
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxRecDepth 4096
namespace HeapV2StepCerts.C3
open ArmCertWalk ArmBridge.Draft HeapV2StepCerts.RegBind

theorem regBind_of_regs {p : HeapV2E17.Pins} {k : Nat} {x y : NativeState}
    (gpr : y.regs.gpr = x.regs.gpr) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) (h : RegBind p k x) : RegBind p k y := by
  intro b mem
  have hb := h b mem
  cases hr : b.1 with
  | x i => rw [hr] at hb; simpa only [regVal, gpr] using hb
  | sp => rw [hr] at hb; simpa only [regVal, sp] using hb

/-- The memory step's addressing: base register and constant offset. -/
def accessAt (k : Nat) : Option (Reg × Int) := (accessTable.find? (·.1 == k)).map (·.2)

def accessAtCheck (e : Nat × Nat × Int × Nat × Bool) : Bool :=
  match accessAt e.1 with
  | some a => (binds e.1).any fun b => b.1 == a.1 && b.2.1 == e.2.1 && b.2.2 + a.2 == e.2.2.1
  | none => false

theorem accessAt_ok : HeapV2Plan.symbolicAccesses.all accessAtCheck = true := by decide +kernel

theorem va_of_bind {p : HeapV2E17.Pins} {s : NativeState} {e : Nat × Nat × Int × Nat × Bool}
    (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 s) {r : Reg} {off : Int}
    (hat : accessAt e.1 = some (r, off)) : regVal s r + BitVec.ofInt 64 off = HeapV2E17.dataVA p e := by
  have chk := List.all_eq_true.1 accessAt_ok e member
  unfold accessAtCheck at chk
  rw [hat] at chk
  obtain ⟨b, bmem, bcond⟩ := List.any_eq_true.1 chk
  simp only [Bool.and_eq_true, beq_iff_eq] at bcond
  obtain ⟨⟨hr, hp⟩, hc⟩ := bcond
  rw [← hr, bound b bmem, ← BitVec.ofInt_add, hp, Int.add_assoc, hc]
  rfl

/-- Per-descriptor access data at a plan data VA, from closed membership. -/
theorem access_of_closed {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} {s : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) s)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses)
    {va : BitVec 64} (hva : va = HeapV2E17.dataVA p e) {acc : AccessDescriptor} (shape : DataShape e.2.2.2.2 acc) :
    domain ⟨va, ⟨acc, true⟩, ((e.2.2.2.1 : Nat) : Int)⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨va, ⟨acc, true⟩, ((e.2.2.2.1 : Nat) : Int)⟩,
        CurrentS1AccessAt spec config rows mapping ⟨va, ⟨acc, true⟩, ((e.2.2.2.1 : Nat) : Int)⟩ data s := by
  have permitted : HeapV2E17.Permitted p base va acc ((e.2.2.2.1 : Nat) : Int) :=
    Or.inl ⟨e, member, hva, rfl, shape⟩
  obtain ⟨⟨va', ⟨raw, aligned⟩, size⟩, hva', hraw, haligned, hsize, inDomain, data, current⟩ :=
    closed va acc true _ permitted
  simp only at hva' hraw haligned hsize
  subst hva' hraw haligned hsize
  exact ⟨inDomain, data, current⟩

/-- Static (deployment) check of one plan data access: mapped below 2^56, not MMIO, outside the
table footprint, and for 16-byte accesses the upper half contiguous and not MMIO. -/
def dataOK (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint)
    (e : Nat × Nat × Int × Nat × Bool) : Bool :=
  match mapping (HeapV2E17.dataVA p e) with
  | none => false
  | some n => decide (n + e.2.2.2.1 < 2 ^ 56) && checkMappedNotMMIO mapping (HeapV2E17.dataVA p e) &&
      (List.range e.2.2.2.1).all (fun i => !(fp.slots.any fun slot => decide (slot ≤ n + i) && decide (n + i < slot + fp.width))) &&
      (e.2.2.2.1 != 16 || (mapping (plus8 (HeapV2E17.dataVA p e)) == some (n + 8) &&
        checkMappedNotMMIO mapping (plus8 (HeapV2E17.dataVA p e))))

def DataStatic (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (fp : Footprint) : Prop :=
  HeapV2Plan.symbolicAccesses.all (dataOK p mapping fp) = true

structure DataFacts (mapping : BitVec 64 → Option Nat) (fp : Footprint) (va : BitVec 64) (size : Nat) (pa : BitVec 56) : Prop where
  bound : pa.toNat + size < 2 ^ 56
  mapped : mapping va = some pa.toNat
  mmio : MemM1.MemReadIF.NotMMIO pa
  outside : ∀ i < size, ¬ fp.byte (pa.toNat + i)
  upper : size = 16 → mapping (plus8 va) = some (pa.toNat + 8) ∧ MappedNotMMIO mapping (plus8 va)

theorem data_facts {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {fp : Footprint}
    (static : DataStatic p mapping fp) {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) :
    ∃ pa : BitVec 56, DataFacts mapping fp (HeapV2E17.dataVA p e) e.2.2.2.1 pa := by
  have ok := List.all_eq_true.1 static e member
  unfold dataOK at ok
  split at ok
  · exact absurd ok (by decide)
  · next n hn =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨small, mmioChk⟩, outsideChk⟩, upperChk⟩ := ok
    have hpa : (BitVec.ofNat 56 n).toNat = n := by simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨BitVec.ofNat 56 n, ⟨by rw [hpa]; exact small, by rw [hpa]; exact hn, checkMappedNotMMIO_sound mmioChk _ (by rw [hpa]; exact hn), ?_, ?_⟩⟩
    · intro i hi inTable
      have entry := List.all_eq_true.1 outsideChk i (List.mem_range.2 hi)
      obtain ⟨slot, slotMember, low, high⟩ := inTable
      rw [hpa] at low high
      have hit : (fp.slots.any fun slot => decide (slot ≤ n + i) && decide (n + i < slot + fp.width)) = true :=
        List.any_eq_true.2 ⟨slot, slotMember, by simp [low, high]⟩
      rw [hit] at entry
      exact absurd entry (by decide)
    · intro h16
      rw [h16] at upperChk
      simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at upperChk
      exact ⟨by rw [hpa]; exact upperChk.1, checkMappedNotMMIO_sound upperChk.2⟩

/-- Loaded bytes are present at every plan data PA (ChainInv v3 field). -/
def DataPresent (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (s : NativeState) : Prop :=
  ∀ e ∈ HeapV2Plan.symbolicAccesses, ∀ n, mapping (HeapV2E17.dataVA p e) = some n →
    ∀ i < e.2.2.2.1, (s.mem[n + i]?).isSome

/-- DataPresent carry: any step that keeps present bytes present. -/
theorem DataPresent.carry {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {x y : NativeState}
    (keep : ∀ a : Nat, (x.mem[a]?).isSome → (y.mem[a]?).isSome) (h : DataPresent p mapping x) : DataPresent p mapping y :=
  fun e mem n hn i hi => keep _ (h e mem n hn i hi)

/-- Present bytes assemble into a little-endian value. -/
theorem exists_value (f : Nat → Option (BitVec 8)) :
    ∀ n, (∀ i < n, (f i).isSome) → ∃ v : BitVec (8 * n), ∀ i < n, f i = some (v.extractLsb' (8 * i) 8)
  | 0, _ => ⟨0#0, fun i hi => absurd hi (by omega)⟩
  | n + 1, h => by
    obtain ⟨v, hv⟩ := exists_value f n (fun i hi => h i (by omega))
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h n (by omega))
    refine ⟨BitVec.cast (by omega) (BitVec.append b v), fun i hi => ?_⟩
    by_cases hin : i < n
    · rw [hv i hin]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, BitVec.append_eq, BitVec.getLsbD_append]
      have : 8 * i + j < 8 * n := by omega
      simp [hj, this]
    · have hi' : i = n := by omega
      subst hi'
      rw [hb]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, BitVec.append_eq, BitVec.getLsbD_append]
      have : ¬ 8 * i + j < 8 * i := by omega
      simp [hj, this]

#print axioms va_of_bind
#print axioms access_of_closed
#print axioms data_facts
#print axioms exists_value
end HeapV2StepCerts.C3
