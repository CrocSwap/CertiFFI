import HeapDefaultTagCheck.Halves
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemPair8R
open NativeMteTagCheck ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace HeapDefaultTagCheck.PairRead
abbrev State := NativeMteTagCheck.State
private theorem read_split {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (h8 : A.toNat % 8 = 0) (h16 : A.toNat % 16 ≠ 0) (acc : AccessDescriptor)
    (hA : MemM1.MemReadD2.AccDR2 acc) (shape : DataShape false acc)
    (perAcc : ∀ prepared, DataShape false prepared → PairAccess spec config rows mapping A prepared s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs s.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 2) (el : acc.el = EL0) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping A = some pa1.toNat) (mapped2 : mapping (plus8 A) = some pa2.toNat)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ prepared, DataShape false prepared → NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (value : BitVec (16 * 8))
    (bytes1 : ∀ i < 8, s.mem[pa1.toNat + i]? = some (value.extractLsb' (8 * i) 8))
    (bytes2 : ∀ i < 8, s.mem[pa2.toNat + i]? = some (value.extractLsb' (8 * (i + 8)) 8)) :
    ∃ t draws, Mem_read__1 A 16 acc true s = .ok value t ∧ t.regs = s.regs ∧ t.mem = s.mem ∧
      PairEvents spec A pa1 pa2
        (.memRead pa1.toNat 16 (some A.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa1.toNat 8 (some A.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa2.toNat 8 (some (plus8 A).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        s.events t.events ∧
      ChoiceDelta s t draws ∧ draws ≤ 2 := by
  have hb8 : (BitVec.addInt A ((8 : Nat) : Int)).toNat % 8 = 0 := by
    rw [addInt8]; simp [BitVec.toNat_add]; omega
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have e5 := MemM1.MemReadD2.lse2_on s3 (by rw [F3.1]; exact lse2)
  have hai := allIn16_false A h8 h16 s3
  rcases occ_normal 1644 s3 with ⟨l3, s4, e6, f4⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s4 with ⟨b2, s5, e7, f5⟩
  rcases occ_normal 1645 s5 with ⟨l4, s6, e8, f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s6 with ⟨b3, s7, e9, f7⟩
  have F7 := frame_trans (frame_trans (frame_trans (frame_trans F3 f4) f5) f6) f7
  obtain ⟨rc3, e10⟩ : ∃ b, HaveLRCPC3Ext () s7 = .ok b s7 := ⟨_, rfl⟩
  have dF3 : ChoiceDelta s s3 0 := choice_delta_trans
    (choice_delta_trans (TagCheckFrames.occ_frame 1640 (by decide) s l1 s1 e1)
      (TagCheckFrames.occ_frame 1641 (by decide) s1 l2 s2 e3))
    (TagCheckFrames.bits_preserves _ _ s2 b1 s3 e4)
  have dF7 : ChoiceDelta s s7 0 := choice_delta_trans
    (choice_delta_trans (choice_delta_trans (choice_delta_trans dF3
      (TagCheckFrames.occ_frame 1644 (by decide) s3 l3 s4 e6))
      (TagCheckFrames.bits_preserves _ _ s4 b2 s5 e7))
      (TagCheckFrames.occ_frame 1645 (by decide) s5 l4 s6 e8))
      (TagCheckFrames.bits_preserves _ _ s6 b3 s7 e9)
  have allowed := Access.status_at statusRows (choice_delta_refl s) (by decide)
  obtain ⟨ad1,mid1,x,draws1,ex,traffic1,_,evx,rx,mx,dx,bound1⟩ :=
    Halves.half_read spec config rows mapping s s7 ⟨F7.1,F7.2.1,F7.2.2,dF7⟩ A h8 acc hA shape
      (fun prepared hp => ((perAcc prepared hp).2 h16).1) current mode debug post catalogue controls allowed el
      dcache pa1 mapped1 mmio1 raw noUpd (value.extractLsb' 0 64)
      (fun i hi => by rw [lo_byte value i hi]; exact bytes1 i hi)
  have allowedX := Access.status_at statusRows dx (by omega)
  obtain ⟨ad2,mid2,y,draws2,ey,traffic2,_,evy,ry,my,dy,bound2⟩ :=
    Halves.half_read spec config rows mapping x x ⟨rfl,rfl,rfl,choice_delta_refl x⟩
      (plus8 A) hb8 acc hA shape
      (fun prepared hp => by
        obtain ⟨m,d,q⟩ := ((perAcc prepared hp).2 h16).2
        exact ⟨m,d,q.of_regs rx⟩)
      (current_s1_frame current rx mx) (by rw [rx]; exact mode) (by rw [rx]; exact debug)
      (by rw [rx]; exact post) catalogue (Halves.default_of_regs controls rx) allowedX el
      (by rw [rx]; exact dcache) pa2 mapped2 mmio2 (by rw [mx]; exact raw)
      (by rw [rx]; exact noUpd) (value.extractLsb' 64 64)
      (fun i hi => by rw [mx, hi_byte value i hi]; exact bytes2 i hi)
  have ry0 : y.regs = s.regs := ry.trans rx
  have my0 : y.mem = s.mem := my.trans mx
  have ex' : AArch64_MemSingle_read__1 A (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false s7
      = .ok (value.extractLsb' 0 64) x := ex
  have ey' : AArch64_MemSingle_read__1 (BitVec.addInt A ((8 : Nat) : Int))
      (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false x
      = .ok (value.extractLsb' 64 64) y := ey
  have hPy : PostRegs y.regs := ry0 ▸ post
  rcases MemM1.MemReadDBE.be_false y hPy.el0 hPy.nrw hPy.noRME hPy.vhe hPy.aa64el0 hPy.ns hPy.e2h
    hPy.tge hPy.e0e with ⟨t, e11, f11⟩
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 A h8
  have hsz2 : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by
    decide
  have hh8 : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8)) = true := by
    decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  have kind := MemM1.MemReadD2.kind_eq2 acc hA
  have dBE := TagCheckFrames.bigEndian_preserves .AccessType_GPR y false t e11
  have delta : ChoiceDelta s t (draws1+draws2) := by
    simpa only [Nat.add_zero] using choice_delta_trans (choice_delta_trans dx dy) dBE
  refine ⟨t,draws1+draws2,?_,f11.1.trans ry0,f11.2.1.trans my0,?_,delta,by omega⟩
  · unfold Mem_read__1 Mem_read__2 AArch64_MemSingle_read
    simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
      PreSail.assert, hsz2, hh8, hhalf, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ex', ey', hA.gpr, e11, hal,
      hai, hga, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, Bool.and_true, Bool.true_and, ↓reduceIte, ite_self,
      Sail.BitVec.castWidth_eq]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp (disch := decide) only [cw_toNat, BitVec.append_eq]
    rw [← join_toNat value, BitVec.toNat_append, BitVec.toNat_append]
    have hw : Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int)) * 8
        = 64 := by decide
    rw [hw]
    rfl
  · exact Or.inr ⟨h16,ad1,mid1,ad2,mid2,traffic1,by rw [kind] at evx; rw [← evx]; exact traffic2,
      by rw [f11.2.2,evy,kind]⟩

theorem loadPair_noupdate {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (A : BitVec 64) (h8 : A.toNat % 8 = 0) (acc : AccessDescriptor)
    (hA : MemM1.MemReadD2.AccDR2 acc) (shape : DataShape false acc)
    (perAcc : ∀ prepared, DataShape false prepared → PairAccess spec config rows mapping A prepared s)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs s.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 2) (el : acc.el = EL0) (lse2 : s.regs.FeatureImpl[111] = true)
    (dcache : currentDCache s.regs = true)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping A = some pa1.toNat) (mapped2 : mapping (plus8 A) = some pa2.toNat)
    (contiguous : A.toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : ∀ prepared, DataShape false prepared → NoUpdateRows {spec.params with haft := hostHAFT s.regs} prepared spec.imageRows = true)
    (value : BitVec (16 * 8))
    (bytes1 : ∀ i < 8, s.mem[pa1.toNat + i]? = some (value.extractLsb' (8 * i) 8))
    (bytes2 : ∀ i < 8, s.mem[pa2.toNat + i]? = some (value.extractLsb' (8 * (i + 8)) 8)) :
    ∃ t draws, Mem_read__1 A 16 acc true s = .ok value t ∧ t.regs = s.regs ∧ t.mem = s.mem ∧
      PairEvents spec A pa1 pa2
        (.memRead pa1.toNat 16 (some A.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa1.toNat 8 (some A.toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa2.toNat 8 (some (plus8 A).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        s.events t.events ∧
      ChoiceDelta s t draws ∧ draws ≤ (if A.toNat % 16 = 0 then 1 else 2) := by
  have kind := MemM1.MemReadD2.kind_eq2 acc hA
  by_cases h16 : A.toNat % 16 = 0
  · have bytes : ∀ i < 16, s.mem[pa1.toNat + i]? = some (value.extractLsb' (8 * i) 8) := by
      intro i hi
      by_cases lo : i < 8
      · exact bytes1 i lo
      · have := bytes2 (i - 8) (by omega)
        rw [contiguous h16, show pa1.toNat + 8 + (i - 8) = pa1.toNat + i by omega,
          show i - 8 + 8 = i by omega] at this
        exact this
    have allowed := Access.status_at statusRows (choice_delta_refl s) (by decide)
    obtain ⟨ad,mid,t,draws,call,traffic,_,events,regs,mem,delta,bound⟩ :=
      DefaultPairNoUpdate.load16 spec config rows mapping s A h16 acc hA shape
        (fun prepared hp => (perAcc prepared hp).1 h16) current mode debug post catalogue controls allowed
        el lse2 dcache pa1 mapped1 mmio1 raw noUpd value bytes
    exact ⟨t,draws,call,regs,mem,Or.inl ⟨h16,ad,mid,traffic,by rw [events,kind]⟩,
      delta,by simpa [h16] using bound⟩
  · obtain ⟨t,draws,run,regs,mem,events,delta,bound⟩ := read_split spec config rows mapping s A h8 h16 acc hA shape
      perAcc current mode debug post catalogue controls statusRows el lse2 dcache pa1 pa2 mapped1 mapped2
      mmio1 mmio2 raw noUpd value bytes1 bytes2
    exact ⟨t,draws,run,regs,mem,events,delta,by simpa [h16] using bound⟩

#print axioms loadPair_noupdate
end HeapDefaultTagCheck.PairRead
