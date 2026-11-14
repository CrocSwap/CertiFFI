import NativeAccess.Read
import NativeAccess.Store
import MemM1.MemWriteD6
import MemM1.MemReadDBE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] EStateM Arch.arch_ak
namespace NativeAccess.Logical
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2

theorem result_rebuild {ε σ α : Type} (r : EStateM.Result ε σ α) :
    (match r with | .ok a t => .ok a t | .error e t => .error e t) = r := by
  cases r <;> rfl

theorem checked_nat (n : Nat) : Sail.Int.toNatChecked (n : Int) = n := by
  simp [Sail.Int.toNatChecked]

theorem map_cast_same {n : Nat} (m : SailM (BitVec n)) :
    (Sail.BitVec.castWidth (m := n) <$> m) = m := by
  funext t
  cases h : m t <;> simp only [Functor.map,EStateM.map,h,Sail.BitVec.castWidth_eq]

theorem map_cast_checked (n : Nat) (m : SailM (BitVec (n * 8))) :
    (Sail.BitVec.castWidth (m := Sail.Int.toNatChecked (n : Int) * 8) <$> m) = m := by
  exact map_cast_same m

/-- Actual scalar LDR path selected by LSE2 and within-16 geometry. The
translation receives the original computed alignment flag, including false.
This intermediate rule must be instantiated from current translation facts. -/
theorem read8_lse2 (a : BitVec 64) (fit : Read.Within16 a 8)
    (acc : AccessDescriptor) (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (hlse : p.lse2 = true) (plain : Plain acc)
    (pa : BitVec 56) (data : BitVec (8 * 8)) (hA : AccDR2 acc)
    (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc (IsAligned__1 a ((8 : Nat) : Int)) ((8 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 8, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read a 8 acc s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((8 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have host3 : HostPins s3 := by
    rcases hp.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F3.1] <;> assumption
  have a3 : _get_SCTLR_EL2_Type_A (s3.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F3.1]; exact hp.alignment_disabled
  obtain ⟨s4, ef, ff⟩ : ∃ s4,
      ((if !(IsAligned__1 a ((8 : Nat) : Int)) then AArch64_UnalignedAccessFaults acc a ((8 : Nat) : Int)
        else pure false) : SailM Bool) s3 = .ok false s4 ∧ Frame s3 s4 := by
    cases h : IsAligned__1 a ((8 : Nat) : Int) with
    | false =>
      obtain ⟨u, eu, ru, mu, vu⟩ := plain_unaligned_allowed s3 host3 a3 acc plain a 8
      refine ⟨u, ?_, ru, mu, vu⟩
      simp only [h, Bool.not_false, ite_true]
      exact eu
    | true => exact ⟨s3, by simp only [h, Bool.not_true, Bool.false_eq_true, ite_false]; rfl,
        rfl, rfl, rfl⟩
  simp only [Pure.pure] at ef
  have F4 := frame_trans F3 ff
  have ls4 : s4.regs.FeatureImpl[111] = true := by rw [F4.1, hp.lse2, hlse]
  have e5 : HaveLSE2Ext () s4 = .ok true s4 := by rw [have_lse2, ls4]
  have hai := Read.allIn8_of_fit a fit s4
  rcases Read.single8_within16 a (IsAligned__1 a ((8 : Nat) : Int)) false acc s4 ls4 fit pa data hA
      (by rw [F4.1]; exact hM2) Q
      (fun u fu => hTA u (frame_trans F4 fu)) hio with
    ⟨ad,t1,t,hQ,hP,e6,hte,htr,htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP.post
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0
      hPt.ns hPt.e2h hPt.tge hPt.e0e with ⟨t',e7,f7⟩
  refine ⟨ad,t1,t',hQ,?_,f7.2.2.trans hte,f7.1.trans htr,f7.2.1.trans htm⟩
  have hsz : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8) || (8 : Nat) == 16) = true := by decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  unfold Mem_read Mem_read__2
  simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    ArmFull.assert,PreSail.assert,hsz,e1,e2,e3,e4,ef,e5,hai,e6,hA.gpr,hga,e7, Bool.and_false,Bool.false_and,
    Bool.or_false,Bool.false_or,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    Bool.and_true,Bool.true_and,↓reduceIte,ite_self,Sail.BitVec.castWidth_eq]

/-- Full actual LSE2 one-call 128-bit pair read, with the real half-size
alignment flag and arbitrary highest-address-first parameter. -/
theorem read16_pair_lse2 (a : BitVec 64) (fit : Read.Within16 a 16)
    (acc : AccessDescriptor) (high : Bool) (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (hlse : p.lse2 = true) (plain : Plain acc)
    (pa : BitVec 56) (data : BitVec (16 * 8)) (hA : AccDR2 acc)
    (hM2 : s.regs.FeatureImpl[134] = false)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc (IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int)) ((16 : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧ PostRegs2 t1.regs ∧
      (∀ i < 16, t1.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8)) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_read__2 a 16 acc true high s = .ok data t ∧
      t.events = t1.events.push (.memRead pa.toNat 16 (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) false) ∧
      t.regs = t1.regs ∧ t.mem = t1.mem := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have host3 : HostPins s3 := by
    rcases hp.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F3.1] <;> assumption
  have a3 : _get_SCTLR_EL2_Type_A (s3.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F3.1]; exact hp.alignment_disabled
  obtain ⟨s4, ef, ff⟩ : ∃ s4,
      ((if !(IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int)) then AArch64_UnalignedAccessFaults acc a ((16 : Nat) : Int)
        else pure false) : SailM Bool) s3 = .ok false s4 ∧ Frame s3 s4 := by
    cases h : IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int) with
    | false =>
      obtain ⟨u, eu, ru, mu, vu⟩ := plain_unaligned_allowed s3 host3 a3 acc plain a ((16 : Nat) : Int)
      refine ⟨u, ?_, ru, mu, vu⟩
      simp only [h, Bool.not_false, ite_true]
      exact eu
    | true => exact ⟨s3, by simp only [h, Bool.not_true, Bool.false_eq_true, ite_false]; rfl,
        rfl, rfl, rfl⟩
  simp only [Pure.pure] at ef
  have F4 := frame_trans F3 ff
  have ls4 : s4.regs.FeatureImpl[111] = true := by rw [F4.1, hp.lse2, hlse]
  have e5 : HaveLSE2Ext () s4 = .ok true s4 := by rw [have_lse2, ls4]
  have hai := Read.allIn16_of_fit a fit s4
  rcases Read.single16_within16 a (IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int)) true acc s4 ls4 fit pa data hA
      (by rw [F4.1]; exact hM2) Q
      (fun u fu => hTA u (frame_trans F4 fu)) hio with
    ⟨ad,t1,t,hQ,hP,e6,hte,htr,htm⟩
  have hPt : PostRegs t.regs := htr ▸ hP.post
  rcases MemM1.MemReadDBE.be_false t hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0
      hPt.ns hPt.e2h hPt.tge hPt.e0e with ⟨t',e7,f7⟩
  refine ⟨ad,t1,t',hQ,?_,f7.2.2.trans hte,f7.1.trans htr,f7.2.1.trans htm⟩
  have hsz : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  unfold Mem_read__2
  simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    ArmFull.assert,PreSail.assert,hsz,e1,e2,e3,e4,ef,e5,hai,e6,hA.gpr,hga,e7, Bool.and_false,Bool.false_and,
    Bool.or_false,Bool.false_or,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    Bool.and_true,Bool.true_and,↓reduceIte,ite_self,Sail.BitVec.castWidth_eq]

/-- The alignment flag of the actual logical access, before LSE2 routing. -/
def accessAligned (a : BitVec 64) (n : Nat) (pair : Bool) : Bool :=
  IsAligned__1 a (if pair then (Sail.Int.toNatChecked (Int.ediv n 2) : Int) else (n : Int))

open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD4
open MemM1.MemWriteD5 MemM1.MemWriteD6

/-- Actual logical store, any supported width and original pair/high-first flags,
when the model selects its one-call LSE2 branch. No caller alignment premise. -/
theorem store_lse2 (a : BitVec 64) (n : Nat) (hn : SizeOK n)
    (pair high : Bool) (fit : Read.Within16 a (n : Int))
    (acc : AccessDescriptor) (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (hlse : p.lse2 = true) (plain : Plain acc)
    (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (hT : TagOK acc s.regs) (hLE : LittleEndian acc s)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ u, Frame s u → ∃ ad t1,
      AArch64_TranslateAddress a acc (accessAligned a n pair) (n : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧ TagOK acc t1.regs ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ Mem_set__2 a n acc pair high v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) := by
  rcases occ_normal 1646 s with ⟨l1,s1,e1,f1⟩
  rcases constraint_normal l1 s1 with ⟨c,s2,e2,f2⟩
  rcases occ_normal 1647 s2 with ⟨l2,s3,e3,f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp,s4,e4,f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  have host4 : HostPins s4 := by
    rcases hp.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F4.1] <;> assumption
  have a4 : _get_SCTLR_EL2_Type_A (s4.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F4.1]; exact hp.alignment_disabled
  obtain ⟨s5,ef,ff⟩ : ∃ s5,
      ((if !(accessAligned a n pair) then AArch64_UnalignedAccessFaults acc a (n : Int)
        else pure false) : SailM Bool) s4 = .ok false s5 ∧ Frame s4 s5 := by
    cases h : accessAligned a n pair with
    | false =>
      obtain ⟨u,eu,ru,mu,vu⟩ := plain_unaligned_allowed s4 host4 a4 acc plain a n
      refine ⟨u,?_,ru,mu,vu⟩
      simp only [h,Bool.not_false,ite_true]
      exact eu
    | true => exact ⟨s4,by simp only [h,Bool.not_true,Bool.false_eq_true,ite_false]; rfl,
        rfl,rfl,rfl⟩
  simp only [Pure.pure] at ef
  have F5 := frame_trans F4 ff
  rcases hLE s5 F5 with ⟨s6,e5,f5⟩
  have F6 := frame_trans F5 f5
  have ls6 : s6.regs.FeatureImpl[111] = true := by rw [F6.1,hp.lse2,hlse]
  have e6 : HaveLSE2Ext () s6 = .ok true s6 := by rw [have_lse2,ls6]
  have hai := Store.allIn_of_fit a n hn fit s6
  rcases Store.store_within16 a n hn (accessAligned a n pair) pair acc s6 ls6 fit pa v hA
      (by unfold TagOK; rw [F6.1]; exact hT) Q
      (fun u fu => hTA u (frame_trans F6 fu)) hio with ⟨ad,t1,t,hQ,es,ev,er,em⟩
  have hsimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by
    rw [hA.base.gpr]; rfl
  have hsz : ((((n == 1) || (n == 2)) || (n == 4)) || (n == 8) || (n == 16)) = true := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨ad,t1,t,hQ,?_,ev,er,em⟩
  unfold accessAligned at ef es
  unfold Mem_set__2
  simp only [map_cast_checked,map_cast_same,bind_assoc,Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,hsz,e1,e2,e3,e4,ef,e5,e6,hai,es,hsimd,
    Sail.BitVec.castWidth_eq,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]

/-- The real pure geometry test, with its size assertion discharged. -/
theorem allIn16_run (a : BitVec 64) (s : State) :
    AllInAlignedQuantity a ((16 : Nat) : Int) 16 s =
      .ok (Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) 16 == Align_bits a 16) s := by
  unfold AllInAlignedQuantity
  simp only [show (((16 : Nat) : Int) ≤b 16) = true from rfl,ArmFull.assert,PreSail.assert,
    Bool.true_eq,ite_true,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure]

/-- Canonical two-half read plan. All undefined draws and feature reads are
actual Sail operations, and call order depends on the real LRCPC3 feature. -/
def read16_pairPlan (a : BitVec 64) (acc : AccessDescriptor) (high : Bool) : SailM (BitVec 128) := do
  let _ ← undefined_Constraint (← occLabel 1640) ()
  let _ ← undefined_bitvector_at (← occLabel 1641) (Sail.Int.toNatChecked ((16 : Nat) *i 8))
  let h := Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1644) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1645) (Sail.Int.toNatChecked (h *i 8))
  let (hi,lo) ← if (← HaveLRCPC3Ext ()) && high then do
    let hi ← AArch64_MemSingle_read (BitVec.addInt a h) h acc true
    let lo ← AArch64_MemSingle_read a h acc true
    pure (hi,lo)
  else do
    let lo ← AArch64_MemSingle_read a h acc true
    let hi ← AArch64_MemSingle_read (BitVec.addInt a h) h acc true
    pure (hi,lo)
  let v : BitVec 128 := Sail.BitVec.castWidth (hi +++ lo)
  let be ← BigEndian acc.acctype
  pure (if be then reverse_endianness v else v)

/-- When LSE2 is absent, the actual 8-aligned GPR pair read is two 8-byte
calls, not a 16-byte query even if the address happens to be 16-aligned.
No translation or memory-effect callback occurs in this path identity. -/
theorem read16_pair_split (a : BitVec 64) (ha : a.toNat % 8 = 0)
    (acc : AccessDescriptor) (gpr : acc.acctype = .AccessType_GPR)
    (high : Bool) (s : State)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) 16 == Align_bits a 16)) = false) :
    Mem_read__2 a 16 acc true high s = read16_pairPlan a acc high s := by
  rcases occ_normal 1640 s with ⟨l1,s1,e1,f1⟩
  obtain ⟨c,e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2,s2,e3,f2⟩
  rcases bits_normal (Sail.Int.toNatChecked ((16 : Nat) *i 8)) l2 s2 with ⟨b,s3,e4,f3⟩
  have e4c : undefined_bitvector_at l2 128 s2 = .ok b s3 := e4
  rcases occ_normal 1644 s3 with ⟨l3,s4,e6,f4⟩
  rcases bits_normal (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) *i 8)) l3 s4 with ⟨b3,s5,e7,f5⟩
  have e7c : undefined_bitvector_at l3 64 s4 = .ok b3 s5 := e7
  rcases occ_normal 1645 s5 with ⟨l4,s6,e8,f6⟩
  rcases bits_normal (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) *i 8)) l4 s6 with ⟨b4,s7,e9,f7⟩
  have e9c : undefined_bitvector_at l4 64 s6 = .ok b4 s7 := e9
  have F3 := frame_trans (frame_trans f1 f2) f3
  have e5 : HaveLSE2Ext () s3 = .ok s.regs.FeatureImpl[111] s3 := by rw [have_lse2,F3.1]
  have ea := allIn16_run a s3
  have e10 : HaveLRCPC3Ext () s7 = .ok s7.regs.FeatureImpl[190] s7 := rfl
  have hal : IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2) : Nat) : Int) = true :=
    MemM1.MemReadD.isAligned8 a ha
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  have hal8 : IsAligned__1 a ((8 : Nat) : Int) = true := MemM1.MemReadD.isAligned8 a ha
  have hhs : (((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2) == 1 || Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2) == 2) || Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2) == 4) || Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2) == 8) = true := by decide
  cases hf111 : s.regs.FeatureImpl[111] <;>
  simp only [hf111,Bool.false_and,Bool.true_and] at notJoin e5 <;>
  cases high <;> cases hf : s7.regs.FeatureImpl[190] <;>
  unfold Mem_read__2 read16_pairPlan AArch64_MemSingle_read <;>
  simp only [checked_nat,map_cast_checked,bind_assoc,map_cast_same,Sail.BitVec.castWidth_eq] <;>
  simp only [map_cast_checked,map_cast_same,bind_assoc,Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,checked_nat,hhs,e1,e2,e3,e4,e4c,e5,ea,notJoin,e6,e7,e7c,e8,e9,e9c,e10,hf,gpr,hga,hal,hal8,Sail.BitVec.castWidth_eq,
    Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,Bool.not_false,
    Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]
  all_goals
    first
    | (cases h0 : AArch64_MemSingle_read__1 a (Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) acc true false s7
       case ok lo t =>
         cases h1 : AArch64_MemSingle_read__1 (BitVec.addInt a (Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2))) (Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) acc true false t <;> simp_all only [h0,h1,Sail.BitVec.castWidth_eq] <;> rfl
       case error => simp_all only [h0,Sail.BitVec.castWidth_eq] <;> rfl)
    | (cases h0 : AArch64_MemSingle_read__1 (BitVec.addInt a (Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2))) (Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) acc true false s7
       case ok hi t =>
         cases h1 : AArch64_MemSingle_read__1 a (Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) acc true false t <;> simp_all only [h0,h1,Sail.BitVec.castWidth_eq] <;> rfl
       case error => simp_all only [h0,Sail.BitVec.castWidth_eq] <;> rfl)

/-- Ordered two-half store plan; undefined draws and BigEndian are actual. -/
def store16_pairPlan (a : BitVec 64) (acc : AccessDescriptor) (high : Bool)
    (v : BitVec 128) : SailM Unit := do
  let _ ← undefined_Constraint (← occLabel 1646) ()
  let _ ← undefined_bool_at (← occLabel 1647) ()
  let be ← BigEndian acc.acctype
  let v := if be then reverse_endianness v else v
  let h := Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1650) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1651) (Sail.Int.toNatChecked (h *i 8))
  let hi : BitVec 64 := Sail.BitVec.castWidth (Sail.BitVec.extractLsb v 127 64)
  let lo : BitVec 64 := Sail.BitVec.castWidth (Sail.BitVec.extractLsb v 63 0)
  if (← HaveLRCPC3Ext ()) && high then do
    AArch64_MemSingle_set__1 (BitVec.addInt a h) h acc true false (Sail.BitVec.castWidth hi)
    AArch64_MemSingle_set__1 a h acc true false (Sail.BitVec.castWidth lo)
  else do
    AArch64_MemSingle_set__1 a h acc true false (Sail.BitVec.castWidth lo)
    AArch64_MemSingle_set__1 (BitVec.addInt a h) h acc true false (Sail.BitVec.castWidth hi)

/-- Actual ordered pair-store decomposition for either LSE2 profile whenever
its real join test is false. The 8-alignment premise selects this branch. -/
theorem store16_pair_split (a : BitVec 64) (ha : a.toNat % 8 = 0)
    (acc : AccessDescriptor) (hA : AccDWT acc) (high : Bool) (v : BitVec 128)
    (s : State) (hP : PreW acc s.regs)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) 16 == Align_bits a 16)) = false) :
    Mem_set__2 a 16 acc true high v s = store16_pairPlan a acc high v s := by
  rcases occ_normal 1646 s with ⟨l1,s1,e1,f1⟩
  rcases constraint_normal l1 s1 with ⟨c,s2,e2,f2⟩
  rcases occ_normal 1647 s2 with ⟨l2,s3,e3,f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp,s4,e4,f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  rcases littleEndian_of acc s hA hP s4 F4 with ⟨s5,e5,f5⟩
  have F5 := frame_trans F4 f5
  have e6 : HaveLSE2Ext () s5 = .ok s.regs.FeatureImpl[111] s5 := by rw [have_lse2,F5.1]
  have ea := allIn16_run a s5
  let h := Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)
  rcases occ_normal 1650 s5 with ⟨l3,s6,e7,f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l3 s6 with ⟨b3,s7,e8,f7⟩
  rcases occ_normal 1651 s7 with ⟨l4,s8,e9,f8⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l4 s8 with ⟨b4,s9,e10,f9⟩
  have e11 : HaveLRCPC3Ext () s9 = .ok s9.regs.FeatureImpl[190] s9 := rfl
  have hal : IsAligned__1 a (h : Int) = true := MemM1.MemReadD.isAligned8 a ha
  have hsimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.base.gpr]; rfl
  have hpos : (h >b 0) = true := by decide
  have heq : (((16 : Nat) *i 8) == ((h *i 8) +i (h *i 8))) = true := by decide
  have hsize : (((((h == 1) || (h == 2)) || (h == 4)) || (h == 8)) || (h == 16)) = true := by decide
  dsimp only [h] at hal hpos heq hsize e8 e10
  cases hf111 : s.regs.FeatureImpl[111] <;>
  simp only [hf111,Bool.false_and,Bool.true_and] at notJoin e6 <;>
  cases high <;> cases hf : s9.regs.FeatureImpl[190] <;>
  unfold Mem_set__2 store16_pairPlan <;>
  simp only [checked_nat,bind_assoc,Sail.BitVec.castWidth_eq] <;>
  simp only [Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,checked_nat,e1,e2,e3,e4,e5,e6,ea,notJoin,e7,e8,e9,e10,e11,
    hf,hsimd,hal,hpos,heq,hsize,Sail.BitVec.castWidth_eq,
    Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,Bool.not_false,
    Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]
  all_goals rfl

theorem read16_pair_no_lse (a : BitVec 64) (ha : a.toNat % 8 = 0)
    (acc : AccessDescriptor) (gpr : acc.acctype = .AccessType_GPR)
    (high : Bool) (s : State) (lse : s.regs.FeatureImpl[111] = false) :
    Mem_read__2 a 16 acc true high s = read16_pairPlan a acc high s :=
  read16_pair_split a ha acc gpr high s (by rw [lse]; rfl)

-- Actual constrained choice that determines later low-first byte flags.
drive_spec devpage_native, devpage_complete :
  fun (s : SequentialState Regs oracleChoiceSource) =>
    ((do let c ← ConstrainUnpredictable .Unpredictable_DEVPAGE2
         let u ← get
         pure (c,u.regs,u.mem,u.events)) : SailM _) s

theorem devpage_allowed (s : State) :
    ∃ c u, ConstrainUnpredictable .Unpredictable_DEVPAGE2 s = .ok c u ∧
      (c = .Constraint_FAULT ∨ c = .Constraint_NONE) ∧ Frame s u := by
  obtain ⟨c,u,hu,hallowed⟩ : ∃ c u,
      devpage_native s = .ok (c,s.regs,s.mem,s.events) u ∧
      (c = .Constraint_FAULT ∨ c = .Constraint_NONE) := by
    unfold devpage_native
    split
    · exact ⟨_,_,rfl,Or.inl rfl⟩
    · exact ⟨_,_,rfl,Or.inr rfl⟩
  have hc := (devpage_complete s).trans hu
  cases h : ConstrainUnpredictable .Unpredictable_DEVPAGE2 s with
  | ok b t =>
    simp only [Bind.bind,EStateM.bind,h,get,getThe,MonadStateOf.get,EStateM.get,
      Pure.pure,EStateM.pure] at hc
    have hv := (EStateM.Result.ok.inj hc).1
    obtain ⟨hb,rest⟩ := Prod.mk.inj hv
    have hr := congrArg Prod.fst rest
    have hm := congrArg (fun p => p.2.1) rest
    have he := congrArg (fun p => p.2.2) rest
    subst b
    exact ⟨c,t,rfl,hallowed,hr,hm,he⟩
  | error e t =>
    simp only [Bind.bind,EStateM.bind,h] at hc
    cases hc

/-- Low-first unaligned scalar/pair store plan. The first byte retains false;
DEVPAGE2 selects the actual flags on the remaining byte calls. -/
def store_bytePlan (a : BitVec 64) (n : Nat) (acc : AccessDescriptor) (v : BitVec (n * 8)) : SailM Unit := do
  let _ ← undefined_Constraint (← occLabel 1646) ()
  let _ ← undefined_bool_at (← occLabel 1647) ()
  let _ ← AArch64_UnalignedAccessFaults acc a (n : Int)
  let be ← BigEndian acc.acctype
  let v := if be then reverse_endianness v else v
  let h := Sail.Int.toNatChecked (Int.ediv (n : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1648) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1649) (Sail.Int.toNatChecked (h *i 8))
  let _ ← HaveLRCPC3Ext ()
  AArch64_MemSingle_set a 1 acc false (Sail.BitVec.extractLsb v 7 0)
  let c ← ConstrainUnpredictable .Unpredictable_DEVPAGE2
  let aligned := c == Constraint.Constraint_NONE
  let mut loop_vars := ()
  for i in [1:(n -i 1):1]i do
    let () := loop_vars
    loop_vars ← do
      AArch64_MemSingle_set (BitVec.addInt a i) 1 acc aligned
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb v
          (Sail.Int.toNatChecked ((8 *i i) +i 7)) (Sail.Int.toNatChecked (8 *i i))))
  pure loop_vars

theorem allIn_run (a : BitVec 64) (n : Nat) (hb : ((n : Int) ≤b 16) = true) (s : State) :
    AllInAlignedQuantity a (n : Int) 16 s =
      .ok (Align_bits (BitVec.subInt (BitVec.addInt a (n : Int)) 1) 16 == Align_bits a 16) s := by
  unfold AllInAlignedQuantity
  simp only [hb,ArmFull.assert,PreSail.assert,
    Bool.true_eq,ite_true,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure]

/-- Exact bytewise scalar-store path, including modular VA addition and
choice-dependent flags. No byte-translation or physical-memory hypothesis. -/
theorem store_bytes_low_order (a : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16) (pair high : Bool)
    (unaligned : accessAligned a n pair = false)
    (acc : AccessDescriptor) (hA : AccDWT acc) (plain : Plain acc)
    (v : BitVec (n * 8)) (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (hP : PreW acc s.regs)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a (n : Int)) 1) 16 == Align_bits a 16)) = false)
    (lowOrder : ((s.regs.FeatureImpl[190] && pair) && high) = false) :
    Mem_set__2 a n acc pair high v s = store_bytePlan a n acc v s := by
  rcases occ_normal 1646 s with ⟨l1,s1,e1,f1⟩
  rcases constraint_normal l1 s1 with ⟨c,s2,e2,f2⟩
  rcases occ_normal 1647 s2 with ⟨l2,s3,e3,f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp,s4,e4,f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  have host4 : HostPins s4 := by
    rcases hp.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F4.1] <;> assumption
  have a4 : _get_SCTLR_EL2_Type_A (s4.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F4.1]; exact hp.alignment_disabled
  rcases plain_unaligned_allowed s4 host4 a4 acc plain a (n : Int) with
    ⟨s5,ef,ffr,ffm,ffe⟩
  have F5 := frame_trans F4 ⟨ffr,ffm,ffe⟩
  rcases littleEndian_of acc s hA hP s5 F5 with ⟨s6,e5,f5⟩
  have F6 := frame_trans F5 f5
  have e6 : HaveLSE2Ext () s6 = .ok s.regs.FeatureImpl[111] s6 := by rw [have_lse2,F6.1]
  have hb : ((n : Int) ≤b 16) = true := by rcases hn with rfl | rfl <;> decide
  have ea := allIn_run a n hb s6
  let h := Sail.Int.toNatChecked (Int.ediv (n : Int) 2)
  rcases occ_normal 1648 s6 with ⟨l3,s7,e7,f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l3 s7 with ⟨b3,s8,e8,f7⟩
  rcases occ_normal 1649 s8 with ⟨l4,s9,e9,f8⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l4 s9 with ⟨b4,s10,e10,f9⟩
  have F10 := frame_trans (frame_trans (frame_trans (frame_trans F6 f6) f7) f8) f9
  have e11 : HaveLRCPC3Ext () s10 = .ok s.regs.FeatureImpl[190] s10 := by rw [have_lrcpc3,F10.1]
  have hsimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.base.gpr]; rfl
  have hs : (n >b (1 : Nat)) = true := by rcases hn with rfl | rfl <;> decide
  dsimp only [h] at e8 e10
  unfold accessAligned at unaligned
  cases hf111 : s.regs.FeatureImpl[111] <;>
  simp only [hf111,Bool.false_and,Bool.true_and] at notJoin e6 <;>
  unfold Mem_set__2 store_bytePlan <;>
  simp only [checked_nat,bind_assoc,Sail.BitVec.castWidth_eq] <;>
  simp only [Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,checked_nat,hs,unaligned,e1,e2,e3,e4,ef,e5,e6,ea,notJoin,e7,e8,e9,e10,e11,lowOrder,
    hsimd,Sail.BitVec.castWidth_eq,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]
  all_goals
    cases es : AArch64_MemSingle_set a 1 acc false (Sail.BitVec.extractLsb v 7 0) s10
    case ok x t =>
      rcases devpage_allowed t with ⟨c,u,ec,hc,fc⟩
      cases x
      rcases hc with rfl | rfl <;>
        simp only [es,ec,Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
          Bool.true_or,Bool.false_or,↓reduceIte] <;> rfl
    case error e t => simp only [es]

theorem store_bytes_low (a : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16) (pair : Bool)
    (unaligned : accessAligned a n pair = false)
    (acc : AccessDescriptor) (hA : AccDWT acc) (plain : Plain acc)
    (v : BitVec (n * 8)) (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (hP : PreW acc s.regs)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a (n : Int)) 1) 16 == Align_bits a 16)) = false) :
    Mem_set__2 a n acc pair false v s = store_bytePlan a n acc v s :=
  store_bytes_low_order a n hn pair false unaligned acc hA plain v s p hp hP notJoin
    (by simp only [Bool.and_false])

/-- Low-first byte read plan, preserving the initial undefined value until
all byte slices are overwritten and preserving the actual DEVPAGE2 choice. -/
def read_bytePlan (a : BitVec 64) (n : Nat) (acc : AccessDescriptor) : SailM (BitVec (n * 8)) := do
  let _ ← undefined_Constraint (← occLabel 1640) ()
  let v : BitVec (n * 8) ← Sail.BitVec.castWidth <$> undefined_bitvector_at (← occLabel 1641)
    (Sail.Int.toNatChecked (n *i 8))
  let _ ← AArch64_UnalignedAccessFaults acc a (n : Int)
  let h := Sail.Int.toNatChecked (Int.ediv (n : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1642) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1643) (Sail.Int.toNatChecked (h *i 8))
  let _ ← HaveLRCPC3Ext ()
  let b ← AArch64_MemSingle_read a 1 acc false
  let v := Sail.BitVec.updateSubrange v 7 0 b
  let c ← ConstrainUnpredictable .Unpredictable_DEVPAGE2
  let aligned := c == Constraint.Constraint_NONE
  let mut loop_vars := v
  for i in [1:(Sail.Int.toNatChecked (n -i 1)):1]i do
    let v := loop_vars
    loop_vars ← do
      let b ← AArch64_MemSingle_read (BitVec.addInt a i) 1 acc aligned
      pure (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((8 *i i) +i 7))
        (Sail.Int.toNatChecked (8 *i i)) (Sail.BitVec.castWidth b))
  let v := loop_vars
  let be ← BigEndian acc.acctype
  pure (if be then reverse_endianness v else v)

/-- Exact low-first byte path of the actual scalar/pair read. Translation,
physical-memory and byte-assembly value joins remain separate obligations. -/
theorem read_bytes_low (a : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16) (pair : Bool)
    (unaligned : accessAligned a n pair = false)
    (acc : AccessDescriptor) (hA : AccDR2 acc) (plain : Plain acc)
    (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a (n : Int)) 1) 16 == Align_bits a 16)) = false) :
    Mem_read__2 a n acc pair false s = read_bytePlan a n acc s := by
  rcases occ_normal 1640 s with ⟨l1,s1,e1,f1⟩
  obtain ⟨c,e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2,s2,e3,f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (n *i 8)) l2 s2 with ⟨b,s3,e4,f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have host3 : HostPins s3 := by
    rcases hp.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F3.1] <;> assumption
  have a3 : _get_SCTLR_EL2_Type_A (s3.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F3.1]; exact hp.alignment_disabled
  rcases plain_unaligned_allowed s3 host3 a3 acc plain a (n : Int) with
    ⟨s4,ef,ffr,ffm,ffe⟩
  have F4 := frame_trans F3 ⟨ffr,ffm,ffe⟩
  have e5 : HaveLSE2Ext () s4 = .ok s.regs.FeatureImpl[111] s4 := by rw [have_lse2,F4.1]
  have hb : ((n : Int) ≤b 16) = true := by rcases hn with rfl | rfl <;> decide
  have ea := allIn_run a n hb s4
  let h := Sail.Int.toNatChecked (Int.ediv (n : Int) 2)
  rcases occ_normal 1642 s4 with ⟨l3,s5,e6,f5⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l3 s5 with ⟨b3,s6,e7,f6⟩
  rcases occ_normal 1643 s6 with ⟨l4,s7,e8,f7⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l4 s7 with ⟨b4,s8,e9,f8⟩
  have e10 : HaveLRCPC3Ext () s8 = .ok s8.regs.FeatureImpl[190] s8 := rfl
  have hsimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.gpr]; rfl
  have hs : (n >b (1 : Nat)) = true := by rcases hn with rfl | rfl <;> decide
  have hh : (((h == 1) || (h == 2)) || (h == 4) || (h == 8)) = true := by
    rcases hn with rfl | rfl <;> decide
  dsimp only [h] at e7 e9 hh
  unfold accessAligned at unaligned
  have hff : (Constraint.Constraint_FAULT == Constraint.Constraint_FAULT) = true := rfl
  have hfn : (Constraint.Constraint_FAULT == Constraint.Constraint_NONE) = false := rfl
  have hnn : (Constraint.Constraint_NONE == Constraint.Constraint_NONE) = true := rfl
  have hnf : (Constraint.Constraint_NONE == Constraint.Constraint_FAULT) = false := rfl
  cases hf111 : s.regs.FeatureImpl[111] <;>
  simp only [hf111,Bool.false_and,Bool.true_and] at notJoin e5 <;>
  unfold Mem_read__2 read_bytePlan <;>
  simp only [checked_nat,map_cast_checked,map_cast_same,bind_pure,bind_assoc,Sail.BitVec.castWidth_eq] <;>
  simp only [map_cast_checked,map_cast_same,bind_pure,Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,checked_nat,hs,hh,unaligned,e1,e2,e3,e4,ef,e5,ea,notJoin,e6,e7,e8,e9,e10,
    hsimd,Sail.BitVec.castWidth_eq,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]
  all_goals
    cases es : AArch64_MemSingle_read a 1 acc false s8
    case ok byte t =>
      rcases devpage_allowed t with ⟨c,u,ec,hc,fc⟩
      rcases hc with rfl | rfl <;>
        simp only [hff,hfn,hnn,hnf,result_rebuild,es,ec,Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
          Bool.true_or,Bool.false_or,↓reduceIte] <;> rfl
    case error e t => simp only [es]

/-- Actual high-first byte plan for an unaligned 64-bit GPR pair store.
The LRCPC3 branch keeps aligned=false on both halves; no DEVPAGE2 call occurs. -/
def store16_highBytePlan (a : BitVec 64) (acc : AccessDescriptor) (v : BitVec 128) : SailM Unit := do
  let _ ← undefined_Constraint (← occLabel 1646) ()
  let _ ← undefined_bool_at (← occLabel 1647) ()
  let _ ← AArch64_UnalignedAccessFaults acc a ((16 : Nat) : Int)
  let be ← BigEndian acc.acctype
  let v := if be then reverse_endianness v else v
  let h := Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)
  let _ ← undefined_bitvector_at (← occLabel 1648) (Sail.Int.toNatChecked (h *i 8))
  let _ ← undefined_bitvector_at (← occLabel 1649) (Sail.Int.toNatChecked (h *i 8))
  let _ ← HaveLRCPC3Ext ()
  let hi : BitVec 64 := Sail.BitVec.castWidth (Sail.BitVec.extractLsb v 127 64)
  let lo : BitVec 64 := Sail.BitVec.castWidth (Sail.BitVec.extractLsb v 63 0)
  let _ ← (do
    let mut loop_vars := ()
    for i in [0:(h -i 1):1]i do
      let () := loop_vars
      loop_vars ← do
        AArch64_MemSingle_set (BitVec.addInt (BitVec.addInt a h) i) 1 acc false
          (Sail.BitVec.castWidth (Sail.BitVec.extractLsb hi
            (Sail.Int.toNatChecked ((8 *i i) +i 7)) (Sail.Int.toNatChecked (8 *i i))))
    pure loop_vars)
  let mut loop_vars := ()
  for i in [0:(h -i 1):1]i do
    let () := loop_vars
    loop_vars ← do
      AArch64_MemSingle_set (BitVec.addInt a i) 1 acc false
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb lo
          (Sail.Int.toNatChecked ((8 *i i) +i 7)) (Sail.Int.toNatChecked (8 *i i))))
  pure loop_vars

/-- Actual high-first pair byte-store path. Public LRCPC3=true selects it;
there is no caller alignment/page-crossing or perbyte translation premise. -/
theorem store16_bytes_high (a : BitVec 64) (unaligned : IsAligned__1 a ((8 : Nat) : Int) = false)
    (acc : AccessDescriptor) (hA : AccDWT acc) (plain : Plain acc)
    (v : BitVec 128) (s : State) (p : AccessProfile) (hp : ProfileAt p s)
    (lrcpc3 : p.lrcpc3 = true) (hP : PreW acc s.regs)
    (notJoin : (s.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) 16 == Align_bits a 16)) = false) :
    Mem_set__2 a 16 acc true true v s = store16_highBytePlan a acc v s := by
  rcases occ_normal 1646 s with ⟨l1,s1,e1,f1⟩
  rcases constraint_normal l1 s1 with ⟨c,s2,e2,f2⟩
  rcases occ_normal 1647 s2 with ⟨l2,s3,e3,f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp,s4,e4,f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  have host4 : HostPins s4 := by
    rcases hp.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F4.1] <;> assumption
  have a4 : _get_SCTLR_EL2_Type_A (s4.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F4.1]; exact hp.alignment_disabled
  rcases plain_unaligned_allowed s4 host4 a4 acc plain a ((16 : Nat) : Int) with
    ⟨s5,ef,ffr,ffm,ffe⟩
  have F5 := frame_trans F4 ⟨ffr,ffm,ffe⟩
  rcases littleEndian_of acc s hA hP s5 F5 with ⟨s6,e5,f5⟩
  have F6 := frame_trans F5 f5
  have e6 : HaveLSE2Ext () s6 = .ok s.regs.FeatureImpl[111] s6 := by rw [have_lse2,F6.1]
  have ea := allIn16_run a s6
  let h := Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)
  rcases occ_normal 1648 s6 with ⟨l3,s7,e7,f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l3 s7 with ⟨b3,s8,e8,f7⟩
  rcases occ_normal 1649 s8 with ⟨l4,s9,e9,f8⟩
  rcases bits_normal (Sail.Int.toNatChecked (h *i 8)) l4 s9 with ⟨b4,s10,e10,f9⟩
  have F10 := frame_trans (frame_trans (frame_trans (frame_trans F6 f6) f7) f8) f9
  have e11 : HaveLRCPC3Ext () s10 = .ok true s10 := by
    rw [have_lrcpc3,F10.1,hp.lrcpc3,lrcpc3]
  have hal : IsAligned__1 a (h : Int) = false := unaligned
  have hsimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.base.gpr]; rfl
  have hs : ((16 : Nat) >b (1 : Nat)) = true := rfl
  have heq : (((16 : Nat) *i 8) == ((h *i 8) +i (h *i 8))) = true := by decide
  dsimp only [h] at e8 e10 hal heq
  cases hf111 : s.regs.FeatureImpl[111] <;>
  simp only [hf111,Bool.false_and,Bool.true_and] at notJoin e6 <;>
  unfold Mem_set__2 store16_highBytePlan <;>
  simp only [checked_nat,bind_assoc,Sail.BitVec.castWidth_eq] <;>
  simp only [Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,checked_nat,hs,heq,hal,e1,e2,e3,e4,ef,e5,e6,ea,notJoin,e7,e8,e9,e10,e11,
    hsimd,Sail.BitVec.castWidth_eq,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]
  all_goals rfl

#print axioms read16_pair_lse2
#print axioms store_bytes_low_order
#print axioms store16_bytes_high
#print axioms read_bytes_low
#print axioms store_bytes_low
#print axioms devpage_allowed
#print axioms devpage_complete
#print axioms store16_pair_split
#print axioms read16_pair_split
#print axioms read8_lse2
#print axioms store_lse2
#print axioms read16_pair_no_lse
end NativeAccess.Logical
