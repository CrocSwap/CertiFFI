-- Memory (certiffi (c3)): fetched-state premises of the pair memory classes (Stp/Ldp on SP,
-- Stp8/Ldp8 on X[Rn]). Every plan pair access is 16-aligned (16-aligned pins, offsets ≡ 0 mod 16),
-- so the single 16-byte LSE2 access is the actual path and PairAccess's split branch is vacuous.
import HeapV2StepCerts.C3Byte
import ArmCertWalk.MemClassStp
import ArmCertWalk.MemClassLdp8
import ArmCertWalk.MemClassStp8
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxRecDepth 4096
namespace HeapV2StepCerts.C3
open ArmCertWalk ArmBridge.Draft HeapV2StepCerts.RegBind

theorem ofInt_aligned (z : Int) (hz : z % 16 = 0) : (BitVec.ofInt 64 z).toNat % 16 = 0 := by
  rw [BitVec.toNat_ofInt]
  have h1 : (z % (2 ^ 64 : Nat)) % 16 = 0 := by rw [Int.emod_emod_of_dvd _ (by decide)]; exact hz
  have h2 : 0 ≤ z % (2 ^ 64 : Nat) := Int.emod_nonneg _ (by decide)
  omega

theorem add_aligned (x : BitVec 64) (off : Int) (h : (x + BitVec.ofInt 64 off).toNat % 16 = 0)
    (hoff : off % 16 = 0) : x.toNat % 16 = 0 := by
  have hy := ofInt_aligned off hoff
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)] at h
  omega

theorem dataVA_aligned {p : HeapV2E17.Pins} {e : Nat × Nat × Int × Nat × Bool}
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0) (hc : e.2.2.1 % 16 = 0) :
    (HeapV2E17.dataVA p e).toNat % 16 = 0 := by
  apply ofInt_aligned
  have := pinAligned e.2.1
  omega

theorem prem_Stp {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (imm7 : BitVec 7) {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0) (hc : e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) :
    (∀ acc, DataShape true acc → domain (MemClass.Stp.query fetched imm7 acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Stp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query fetched imm7 acc) data fetched) ∧
      MemM1.MemWriteD6.PreW acc fetched.regs) ∧
    fetched.regs.SP_EL0.toNat % 16 = 0 ∧ (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0 ∧
    ∃ pa : BitVec 56, mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i) := by
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member bound hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  have hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0 := by rw [hva]; exact dataVA_aligned pinAligned hc
  have hsp : fetched.regs.SP_EL0.toNat % 16 = 0 :=
    add_aligned _ off (by have := hal; simp only [ArmCertMem.LdpEval.ldpAddr, himm] at this; exact this) hoff
  obtain ⟨pa, facts⟩ := data_facts static member
  refine ⟨fun acc shape => ?_, hsp, hal, pa, by rw [hva]; exact facts.mapped, facts.mmio,
    fun i hi => facts.outside i (by omega)⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact ⟨r.1, r.2, preW_of_post2 post acc⟩

theorem prem_Ldp {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (present : DataPresent p mapping fetched)
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (imm7 : BitVec 7) {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0) (hc : e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) :
    (∀ acc, DataShape false acc → domain (MemClass.Ldp.query fetched imm7 acc) ∧
      ∃ data : S1AccessData spec config rows (MemClass.Ldp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldp.query fetched imm7 acc) data fetched) ∧
    fetched.regs.SP_EL0.toNat % 16 = 0 ∧ (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0 ∧
    ∃ pa : BitVec 56, mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ∃ data : BitVec 128, ∀ i < 16, fetched.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8) := by
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member bound hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  have hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0 := by rw [hva]; exact dataVA_aligned pinAligned hc
  have hsp : fetched.regs.SP_EL0.toNat % 16 = 0 :=
    add_aligned _ off (by have := hal; simp only [ArmCertMem.LdpEval.ldpAddr, himm] at this; exact this) hoff
  obtain ⟨pa, facts⟩ := data_facts static member
  obtain ⟨v, hv⟩ := exists_value (fun i => fetched.mem[pa.toNat + i]?) 16
    (fun i hi => present e member pa.toNat facts.mapped i (by omega))
  refine ⟨fun acc shape => ?_, hsp, hal, pa, by rw [hva]; exact facts.mapped, facts.mmio, v, hv⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact r

#print axioms prem_Stp
#print axioms prem_Ldp
theorem pair8_va {p : HeapV2E17.Pins} {s : NativeState} {e : Nat × Nat × Int × Nat × Bool}
    (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 s) (Rn : BitVec 5) (imm7 : BitVec 7) {off : Int}
    (hat : accessAt e.1 = some (.x (rk Rn), off)) (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) :
    s.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3) = HeapV2E17.dataVA p e := by
  have h := va_of_bind member bound hat
  simp only [regVal, rk] at h
  rw [himm, h]

theorem pa2_toNat (pa : BitVec 56) (size : Nat) (hb : pa.toNat + size < 2 ^ 56) (hs : size = 16) :
    (BitVec.ofNat 56 (pa.toNat + 8)).toNat = pa.toNat + 8 := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem prem_Stp8 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (Rn : BitVec 5) (imm7 : BitVec 7) {off : Int} (hat : accessAt e.1 = some (.x (rk Rn), off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hc : e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) :
    (∀ acc, DataShape true acc → PairAccess spec config rows mapping (MemClass.Stp8.pairAddr fetched Rn imm7) acc fetched) ∧
    (∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc → MemM1.MemWriteD6.PreW acc fetched.regs) ∧
    (MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 8 = 0 ∧
    ∃ pa1 pa2 : BitVec 56, mapping (MemClass.Stp8.pairAddr fetched Rn imm7) = some pa1.toNat ∧
      mapping (plus8 (MemClass.Stp8.pairAddr fetched Rn imm7)) = some pa2.toNat ∧
      ((MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8) ∧
      MemM1.MemReadIF.NotMMIO pa1 ∧ MemM1.MemReadIF.NotMMIO pa2 ∧
      (∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i)) ∧
      (∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa2.toNat + i)) := by
  have hva : MemClass.Stp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e := pair8_va member bound Rn imm7 hat himm
  have hal : (MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 16 = 0 := by rw [hva]; exact dataVA_aligned pinAligned hc
  obtain ⟨pa, facts⟩ := data_facts static member
  have h2 := pa2_toNat pa _ facts.bound hsize
  obtain ⟨up, upm⟩ := facts.upper hsize
  refine ⟨fun acc shape => ⟨fun _ => ?_, fun h => absurd hal h⟩, fun acc _ _ => preW_of_post2 post acc,
    by omega, pa, BitVec.ofNat 56 (pa.toNat + 8), by rw [hva]; exact facts.mapped,
    by rw [hva, h2]; exact up, fun _ => h2, facts.mmio, upm _ (by rw [hva, h2] at *; exact up),
    fun i hi => facts.outside i (by omega), fun i hi => by rw [h2, Nat.add_assoc]; exact facts.outside (8 + i) (by omega)⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact r

theorem prem_Ldp8 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (present : DataPresent p mapping fetched)
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (Rn : BitVec 5) (imm7 : BitVec 7) {off : Int} (hat : accessAt e.1 = some (.x (rk Rn), off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hc : e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) :
    (∀ acc, DataShape false acc → PairAccess spec config rows mapping (MemClass.Ldp8.pairAddr fetched Rn imm7) acc fetched) ∧
    (MemClass.Ldp8.pairAddr fetched Rn imm7).toNat % 8 = 0 ∧
    ∃ pa1 pa2 : BitVec 56, mapping (MemClass.Ldp8.pairAddr fetched Rn imm7) = some pa1.toNat ∧
      mapping (plus8 (MemClass.Ldp8.pairAddr fetched Rn imm7)) = some pa2.toNat ∧
      ((MemClass.Ldp8.pairAddr fetched Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8) ∧
      MemM1.MemReadIF.NotMMIO pa1 ∧ MemM1.MemReadIF.NotMMIO pa2 ∧
      ∃ data : BitVec 128,
        (∀ i < 8, fetched.mem[pa1.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8)) ∧
        (∀ i < 8, fetched.mem[pa2.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * (i + 8)) 8)) := by
  have hva : MemClass.Ldp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e := pair8_va member bound Rn imm7 hat himm
  have hal : (MemClass.Ldp8.pairAddr fetched Rn imm7).toNat % 16 = 0 := by rw [hva]; exact dataVA_aligned pinAligned hc
  obtain ⟨pa, facts⟩ := data_facts static member
  have h2 := pa2_toNat pa _ facts.bound hsize
  obtain ⟨up, upm⟩ := facts.upper hsize
  obtain ⟨v, hv⟩ := exists_value (fun i => fetched.mem[pa.toNat + i]?) 16
    (fun i hi => present e member pa.toNat facts.mapped i (by omega))
  refine ⟨fun acc shape => ⟨fun _ => ?_, fun h => absurd hal h⟩,
    by omega, pa, BitVec.ofNat 56 (pa.toNat + 8), by rw [hva]; exact facts.mapped,
    by rw [hva, h2]; exact up, fun _ => h2, facts.mmio, upm _ (by rw [hva, h2] at *; exact up),
    v, fun i hi => hv i (by omega), fun i hi => by rw [h2, Nat.add_assoc, Nat.add_comm 8 i]; exact hv (i + 8) (by omega)⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact r

#print axioms prem_Stp8
#print axioms prem_Ldp8
end HeapV2StepCerts.C3
