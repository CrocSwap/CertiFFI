import M1a.Entry20
import JointEL10.FieldsCore
import JointEL10.Get20
import JointEL10.Regime20
import JointEL10.Normal2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a
open S1OuterSetup S1LogicalReference

/- Deliverable-2 walk side: a general logical Path ending in a level-3
   page leaf, over exact byte realization, gives the exact-bytes Walk20 path. -/

theorem decoded_encode (ee : BitVec 1) (d : BitVec 64) :
    S2FetchFrame.decoded ee (S2Endian.encode ee d) = d := by
  rw [S1ResourcePath.decoded_eq_encode, S2Endian.encode_involutive]

theorem of_path20 (wp : S1TTWParams) (va : BitVec 64) (mem : S1ByteMemory.Memory)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (wp.ee == 1#1) (wp.pie == 1#1)
      (wp.ha == 1#1) (wp.hd == 1#1) (fun a => mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt (wp.ee == 1#1) (fun a => mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    {level bits : Nat} {base : BitVec 48} {result : PathEnd}
    (path : Path observe (S2PhysicalSizeFrame.value wp.ps).toNat va level bits base result) :
    ∀ (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64),
      result = .leaf 3 slotL physL vL → bits = 9 →
      ∀ slot : FullAddress, slot.address.toNat = entryAddress base va level bits →
      ∃ (n : Nat) (S : FullAddress) (D : BitVec 64),
        Walk20 wp va mem n (level : Int) slot 3 S D ∧
        S.address.toNat = physL.address.toNat ∧
        BytesAt (wp.ee == 1#1) (fun a => mem[a]?) physL (S2FetchFrame.decoded wp.ee D) := by
  induction path with
  | invalid => intro _ _ _ hres; cases hres
  | range => intro _ _ _ hres; cases hres
  | leaf lv bs b physical v hl aligned present kind =>
    intro slotL physL vL hres _ slot hslot
    cases hres
    rcases realizes _ physical v present with ⟨d, hb, hv⟩
    have ha := available _ physical v present
    have he : slot.address = physical.address :=
      BitVec.eq_of_toNat_eq (hslot.trans (identity _ physical v present).symm)
    have hdesc : S2ByteMemory.DescAt mem slot.address.toNat (S2Endian.encode wp.ee d) := by
      rw [he]; exact (S1ReferenceEncoding.bytes_iff wp.ee mem physical d).mp hb
    have hk := S1ReferenceKind.view_kind _ _ _ d v hv 3 (by omega)
    have hleaf : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee (S2Endian.encode wp.ee d))
        ((3 : Nat) : Int) = .DescriptorType_Leaf := by
      rw [decoded_encode]
      cases h : S1DecodeFacts.classify d ((3 : Nat) : Int) <;> simp_all
    refine ⟨1, slot, S2Endian.encode wp.ee d, Walk20.leaf ⟨by omega, by omega⟩ (by rw [he]; exact ha.2.2)
      hdesc hleaf, by rw [he], by rw [decoded_encode]; exact hb⟩
  | table lv bs b physical v res hl aligned present kind inRange next ih =>
    intro slotL physL vL hres hbits slot hslot
    rcases realizes _ physical v present with ⟨d, hb, hv⟩
    have ha := available _ physical v present
    have he : slot.address = physical.address :=
      BitVec.eq_of_toNat_eq (hslot.trans (identity _ physical v present).symm)
    have hdesc : S2ByteMemory.DescAt mem slot.address.toNat (S2Endian.encode wp.ee d) := by
      rw [he]; exact (S1ReferenceEncoding.bytes_iff wp.ee mem physical d).mp hb
    have hk := S1ReferenceKind.view_kind _ _ _ d v hv lv (by omega)
    have htable : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee (S2Endian.encode wp.ee d))
        (lv : Int) = .DescriptorType_Table := by
      rw [decoded_encode]
      cases h : S1DecodeFacts.classify d (lv : Int) <;> simp_all
    have hn := S1EntryNextGeometry.next_slot wp d va lv hl
    rw [show S1ResourcePath.view wp d = v from hv] at hn
    rcases ih slotL physL vL hres rfl (S1ResourcePath.nextSlot va (lv : Int) d) hn with
      ⟨n, S, D, hrest, hS, hbytes⟩
    refine ⟨n + 1, S, D, ?_, hS, hbytes⟩
    rw [show S2FetchFrame.decoded wp.ee (S2Endian.encode wp.ee d) = d from decoded_encode _ _] at htable
    refine Walk20.table ⟨by omega, by omega⟩ (by rw [he]; exact ha.2.2) hdesc
      (by rw [decoded_encode]; exact htable) ?_ ?_ ?_
    · rw [decoded_encode]
      apply (S1EntryRangeGeometry.in_range wp _).mpr
      rw [hn]; exact inRange
    · rw [decoded_encode]; exact htab _ physical v d present hb lv kind
    · rw [decoded_encode]
      simpa only [Int.natCast_add, Int.natCast_one] using hrest

#print axioms of_path20

/-- Deliverable-2 walk result (EL2&0, lower range, page leaf at level 3): from a
    general logical Path over exactly realized table bytes, the actual S1Walk returns
    the normal leaf result for the descriptor actually stored at the leaf slot. -/
theorem walk_result_path (c : Context) (f : FaultRecord) (s : State)
    (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (hvr : AArch64_GetVARange c.va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hRootIn : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
      55 (S2PhysicalSizeFrame.value c.wp.ps)) = false)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
      (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64)
    (path : Path observe (S2PhysicalSizeFrame.value c.wp.ps).toNat c.va 0 9
      ((S1EntryRoot.base c.wp s.regs c.regime c.va).setWidth 48) (.leaf 3 slotL physL vL))
    (hleaf : ∀ d, BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) physL d →
      S1Contiguous.bit d = 0#1 ∧ BitVec.join1 [BitVec.access d 10] = 1#1 ∧
      ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base d 3 →
        (!is_zero_subrange (S1StageOA.address c.va v).address 55
          (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ (D : BitVec 64) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) (t : State),
      BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) physL (S2FetchFrame.decoded c.wp.ee D) ∧
      AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧ PostR c s D r t := by
  have hroot := S1EntryRootGeometry.root_slot c.wp s.regs c.regime c.va c.d128 c.tg hTx
  rcases of_path20 c.wp c.va s.mem observe available realizes identity htab path
    slotL physL vL rfl rfl (S1EntryRoot.slot c.wp s.regs c.regime c.va) hroot with
    ⟨n, S, D, hw, _, hbytes⟩
  rcases hleaf _ hbytes with ⟨hc, haf, hoa⟩
  rcases walk_result c f s n hEL20 hHaft hvr hEPD0 hReady hFault hCache hTx hStart hRootIn
    hw rfl hc haf hoa with ⟨r, t, hr, hp⟩
  exact ⟨D, r, t, hbytes, hr, hp⟩

#print axioms walk_result_path
end ArmCert.Eval.M1a
