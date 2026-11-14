import HeapDefaultTagCheck.Halves
import NaturalStores
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemPair8R MemM1.MemWriteD1 MemM1.MemWriteD4 MemM1.MemWriteD5 MemM1.MemWriteD6
open NativeMteTagCheck ReleaseProfile MemM1.MemWriteD7
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace HeapDefaultTagCheck.PairStore
abbrev State := NativeMteTagCheck.State
private theorem store_split {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (h8 : A.toNat % 8 = 0) (h16 : A.toNat % 16 ≠ 0) (acc : AccessDescriptor)
    (hA : MemM1.MemWriteD5.AccDWT acc) (shape : DataShape true acc)
    (perAcc : ∀ prepared, DataShape true prepared → PairAccess spec config rows mapping A prepared s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs s.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 2) (el : acc.el = EL0)
    (lse2 : s.regs.FeatureImpl[111] = true) (dcache : currentDCache s.regs = true)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping A = some pa1.toNat) (mapped2 : mapping (plus8 A) = some pa2.toNat)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ prepared, DataShape true prepared → NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (value : BitVec (16 * 8)) :
    ∃ t draws, Mem_set__1 A 16 acc true value s = .ok () t ∧ t.regs = s.regs ∧
      t.mem = MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold s.mem pa1.toNat 8 (fun j => value.extractLsb' (8 * j) 8))
        pa2.toNat 8 (fun j => value.extractLsb' (8 * (j + 8)) 8) ∧
      PairEvents spec A pa1 pa2
        (.memWrite pa1.toNat 16 (some A.toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) value)) none)
        (.memWrite pa1.toNat 8 (some A.toNat) MemM1.MemWriteD4.akPlain (some (value.extractLsb' 0 64)) none)
        (.memWrite pa2.toNat 8 (some (plus8 A).toNat) MemM1.MemWriteD4.akPlain (some (value.extractLsb' 64 64)) none)
        s.events t.events ∧
      ChoiceDelta s t draws ∧ draws ≤ 2 := by
  have hb8 : (BitVec.addInt A ((8 : Nat) : Int)).toNat % 8 = 0 := by
    rw [addInt8]; simp [BitVec.toNat_add]; omega
  rcases occ_normal 1646 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c,e2⟩ := DefaultPrefix.constraint_total l1 s1
  let s2 := s1
  have f2 : Frame s1 s2 := ⟨rfl,rfl,rfl⟩
  rcases occ_normal 1647 s2 with ⟨l2, s3, e3, f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp, s4, e4, f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  rcases ReleaseProfile.NaturalStores.littleEndian acc s hA post s4 F4 with ⟨s5, e5, f5⟩
  have F5 := frame_trans F4 f5
  have e6 := MemM1.MemWriteD5.lse2_on s5 (by rw [F5.1]; exact lse2)
  have hai := allIn16_false A h8 h16 s5
  rcases occ_normal 1650 s5 with ⟨l3, s6, e7, f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s6 with ⟨b2, s7, e8, f7⟩
  rcases occ_normal 1651 s7 with ⟨l4, s8, e9, f8⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s8 with ⟨b3, s9, e10, f9⟩
  have F9 := frame_trans (frame_trans (frame_trans (frame_trans F5 f6) f7) f8) f9
  obtain ⟨rc3, e11⟩ : ∃ b, HaveLRCPC3Ext () s9 = .ok b s9 := ⟨_, rfl⟩
  have dF4 : ChoiceDelta s s4 0 := choice_delta_trans
    (choice_delta_trans (choice_delta_trans (TagCheckFrames.occ_frame 1646 (by decide) s l1 s1 e1)
      (TagCheckFrames.constraint_preserves _ s1 c s2 e2))
      (TagCheckFrames.occ_frame 1647 (by decide) s2 l2 s3 e3))
      (TagCheckFrames.bool_preserves _ s3 jp s4 e4)
  have dF5 : ChoiceDelta s s5 0 := choice_delta_trans dF4
    (TagCheckFrames.bigEndian_preserves acc.acctype s4 false s5 e5)
  have dF9 : ChoiceDelta s s9 0 := choice_delta_trans
    (choice_delta_trans (choice_delta_trans (choice_delta_trans dF5
      (TagCheckFrames.occ_frame 1650 (by decide) s5 l3 s6 e7))
      (TagCheckFrames.bits_preserves _ _ s6 b2 s7 e8))
      (TagCheckFrames.occ_frame 1651 (by decide) s7 l4 s8 e9))
      (TagCheckFrames.bits_preserves _ _ s8 b3 s9 e10)
  have allowed := Access.status_at statusRows (choice_delta_refl s) (by decide)
  obtain ⟨ad1,mid1,x,draws1,ex,traffic1,_,evx,rx,mx,dx,bound1⟩ :=
    Halves.half_set spec config rows mapping s s9 ⟨F9.1,F9.2.1,F9.2.2,dF9⟩ A 8 (by unfold SizeOK; omega) h8
      acc hA shape el catalogue controls allowed (value.extractLsb' 0 64)
      (fun prepared hp => ((perAcc prepared hp).2 h16).1)
      current mode post debug dcache pa1 mapped1 raw noUpd mmio1
  have mx' : x.mem = wfold s.mem pa1.toNat 8 (fun j => value.extractLsb' (8*j) 8) := by
    rw [mx]
    unfold wfold
    congr 2
    funext j
    exact Prod.ext rfl (lo_byte value j.val j.isLt)
  have allowedX := Access.status_at statusRows dx (by omega)
  obtain ⟨currentX,rawX⟩ := current_after_store8 current raw pa1 _ outside1 rx mx'
  obtain ⟨ad2,mid2,t,draws2,ey,traffic2,_,evy,ry,my,dy,bound2⟩ :=
    Halves.half_set spec config rows mapping x x ⟨rfl,rfl,rfl,choice_delta_refl x⟩ (plus8 A) 8
      (by unfold SizeOK; omega) hb8 acc hA shape el catalogue (Halves.default_of_regs controls rx) allowedX
      (value.extractLsb' 64 64)
      (fun prepared hp => by
        obtain ⟨m,d,q⟩ := ((perAcc prepared hp).2 h16).2
        exact ⟨m,d,q.of_regs rx⟩)
      currentX (by rw [rx]; exact mode) (by rw [rx]; exact post) (by rw [rx]; exact debug)
      (by rw [rx]; exact dcache) pa2 mapped2 rawX (by rw [rx]; exact noUpd) mmio2
  have my' : t.mem = wfold x.mem pa2.toNat 8 (fun j => value.extractLsb' (8*(j+8)) 8) := by
    rw [my]
    unfold wfold
    congr 2
    funext j
    exact Prod.ext rfl (hi_byte value j.val j.isLt)
  have delta := choice_delta_trans dx dy
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 A h8
  have hsimd : (BEq.beq acc.acctype AccessType.AccessType_ASIMD) = false := by
    rw [hA.base.gpr]; rfl
  have ex' : AArch64_MemSingle_set__1 A (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false
      (value.extractLsb' 0 64) s9 = .ok () x := ex
  have ey' : AArch64_MemSingle_set__1 (BitVec.addInt A ((8 : Nat) : Int))
      (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false
      (value.extractLsb' 64 64) x = .ok () t := ey
  have kind := MemM1.MemWriteD7.akT acc hA
  refine ⟨t,draws1+draws2,?_,ry.trans rx,by rw [my',mx'],?_,delta,by omega⟩
  dsimp only [s2] at e3
  · unfold Mem_set__1 Mem_set__2
    simp (config := { decide := true }) only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure,
      EStateM.pure, ArmFull.assert, PreSail.assert, hhalf, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
      hal, hai, hsimd, Sail.BitVec.castWidth_eq, Bool.and_false, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true, Bool.true_and,
      ↓reduceIte, ite_self]
    erw [ex']
    simp only []
    erw [ey']
  · refine Or.inr ⟨h16,ad1,mid1,ad2,mid2,traffic1,?_,?_⟩
    · rw [kind, Sail.BitVec.castWidth_eq] at evx
      rw [← evx]
      exact traffic2
    · simpa only [kind, Sail.BitVec.castWidth_eq] using evy

theorem storePair_noupdate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (h8 : A.toNat % 8 = 0) (acc : AccessDescriptor)
    (hA : MemM1.MemWriteD5.AccDWT acc) (shape : DataShape true acc)
    (perAcc : ∀ prepared, DataShape true prepared → PairAccess spec config rows mapping A prepared s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs s.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 2) (el : acc.el = EL0)
    (lse2 : s.regs.FeatureImpl[111] = true) (dcache : currentDCache s.regs = true)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping A = some pa1.toNat) (mapped2 : mapping (plus8 A) = some pa2.toNat)
    (contiguous : A.toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ prepared, DataShape true prepared → NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (value : BitVec (16 * 8)) :
    ∃ t draws, Mem_set__1 A 16 acc true value s = .ok () t ∧ t.regs = s.regs ∧
      t.mem = MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold s.mem pa1.toNat 8 (fun j => value.extractLsb' (8 * j) 8))
        pa2.toNat 8 (fun j => value.extractLsb' (8 * (j + 8)) 8) ∧
      PairEvents spec A pa1 pa2
        (.memWrite pa1.toNat 16 (some A.toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) value)) none)
        (.memWrite pa1.toNat 8 (some A.toNat) MemM1.MemWriteD4.akPlain (some (value.extractLsb' 0 64)) none)
        (.memWrite pa2.toNat 8 (some (plus8 A).toNat) MemM1.MemWriteD4.akPlain (some (value.extractLsb' 64 64)) none)
        s.events t.events ∧
      ChoiceDelta s t draws ∧ draws ≤ (if A.toNat % 16 = 0 then 1 else 2) := by
  by_cases h16 : A.toNat % 16 = 0
  · have allowed := Access.status_at statusRows (choice_delta_refl s) (by decide)
    obtain ⟨ad,mid,t,draws,call,traffic,_,events,regs,mem,delta,bound⟩ :=
      DefaultStoreNoUpdate.pair spec config rows mapping s s ⟨rfl,rfl,rfl,choice_delta_refl s⟩
        A h16 acc hA shape el catalogue controls allowed value lse2
        (fun prepared hp => (perAcc prepared hp).1 h16) current mode post debug dcache pa1 mapped1 raw noUpd mmio1
    refine ⟨t,draws,call,regs,?_,Or.inl ⟨h16,ad,mid,traffic,by rw [events,akT acc hA]⟩,delta,by simpa [h16] using bound⟩
    rw [mem]
    apply Std.ExtHashMap.ext_getElem?
    intro p
    have c := contiguous h16
    simp only [MemM1.MemWriteD1.wfold_get, c, MemM1.MemWriteD4.wbyte]
    by_cases r1 : pa1.toNat ≤ p ∧ p < pa1.toNat + 8
    · have r16 : pa1.toNat ≤ p ∧ p < pa1.toNat + 16 := by omega
      have n8 : ¬ (pa1.toNat + 8 ≤ p) := by omega
      simp only [r16, r1, n8, and_true, and_self, true_and, false_and, ↓reduceIte]
      first | rfl | simp [BitVec.castWidth]
    · by_cases r2 : pa1.toNat + 8 ≤ p ∧ p < pa1.toNat + 8 + 8
      · have r16 : pa1.toNat ≤ p ∧ p < pa1.toNat + 16 := by omega
        have y8 : pa1.toNat + 8 ≤ p := r2.1
        have y16 : p < pa1.toNat + 8 + 8 := r2.2
        simp only [r16, y8, y16, and_true, and_self, true_and, ↓reduceIte]
        have e : p - (pa1.toNat + 8) + 8 = p - pa1.toNat := by omega
        rw [e]
        first | rfl | simp [BitVec.castWidth]
      · have r16 : ¬ (pa1.toNat ≤ p ∧ p < pa1.toNat + 16) := by omega
        simp only [r16, r1, r2, ↓reduceIte]
  · obtain ⟨t,draws,run,regs,mem,events,delta,bound⟩ := store_split spec config rows mapping s A h8 h16 acc hA shape
      perAcc current mode debug post catalogue controls statusRows el lse2 dcache pa1 pa2 mapped1 mapped2
      mmio1 mmio2 outside1 raw noUpd value
    exact ⟨t,draws,run,regs,mem,events,delta,by simpa [h16] using bound⟩

#print axioms storePair_noupdate
end HeapDefaultTagCheck.PairStore
