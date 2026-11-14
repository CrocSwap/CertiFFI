import NativeMte2.Store
import NativeMteTagCheck.Prepare
import NativeMteTagCheck.Transport
import MemM1.MemWriteD5
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace ReleaseProfile.DefaultStores
open NativeMte2
abbrev State := NativeMte2.State
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5
open NativeMte2.Read (Within16)

theorem store_natural (a : BitVec 64) (n : Nat) (hn : SizeOK n) (aligned ispair : Bool) (ha : a.toNat % n = 0)
    (acc : AccessDescriptor) (s : State) (pa : BitVec 56) (v : BitVec (n * 8)) (hA : AccDWT acc)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue s) (hel : acc.el = EL0)
    (Q : AddressDescriptor → State → Prop)
    (hTA : ∀ (prepared : AccessDescriptor) u,
      prepared = { acc with tagchecked := prepared.tagchecked } →
      NativeMteTagCheck.StatusTrace.TraceFrame s u → ∃ ad t1,
      AArch64_TranslateAddress a prepared aligned ((n : Nat) : Int) u = .ok ad t1 ∧
      ad.fault.statuscode = .Fault_None ∧ ad.paddress.address = pa ∧
      ad.memattrs.memtype = .MemType_Normal ∧ ad.memattrs.inner.attrs = MemAttr_WB ∧
      ad.memattrs.outer.attrs = MemAttr_WB ∧
      t1.regs.bank_Bool .SPESampleInFlight = false ∧
      NativeMteTagCheck.DefaultAt catalogue t1 ∧
      (∀ value after, HaveTME () t1 = .ok value after → NativeMteTagCheck.TagStatusOK after) ∧ Q ad t1)
    (hio : NotMMIO pa) :
    ∃ ad t1 t, Q ad t1 ∧ AArch64_MemSingle_set__1 a n acc aligned ispair v s = .ok () t ∧
      t.events = t1.events.push (.memWrite pa.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind acc) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none) ∧
      t.regs = t1.regs ∧
      t.mem = wfold t1.mem pa.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) := by
  obtain ⟨lse, e3⟩ : ∃ b, HaveLSE2Ext () s = .ok b s := ⟨_, rfl⟩
  obtain ⟨m2, eM2⟩ : ∃ b, HaveMTE2Ext () s = .ok b s := ⟨_, rfl⟩
  obtain ⟨prepared, u, e4, preparedEq, fu, _⟩ := NativeMteTagCheck.StatusTrace.prepare_default catalogue a acc s controls hel
  have preparedEl : prepared.el = EL0 := by rw [preparedEq]; exact hel
  have e4if := e4
  simp only [NativeMte2.prepare, eM2,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at e4if
  rcases hTA prepared u preparedEq fu with
    ⟨ad, t1, e5, hf, hpa, hmt, hin, hout, hspe, hDefault, hStatus, hQ⟩
  rcases MemM1.S1T.tme_normal t1 with ⟨tme, t2, e6, f6⟩
  have default2 := hDefault.transport f6
  obtain ⟨t3, eTag, fTag, _⟩ := NativeMteTagCheck.tagcheck_no_abort catalogue a ad prepared t2 default2
    preparedEl (fun _ _ => hStatus tme t2 e6)
  have eTagIf := eTag
  obtain ⟨m7, e7⟩ : ∃ b, HaveMTE2Ext () t2 = .ok b t2 := ⟨_, rfl⟩
  simp only [NativeMteTagCheck.checkedAccess, e7,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at eTagIf
  have hA' : AccDWT prepared := by
    rw [preparedEq]
    exact ⟨⟨hA.base.ss,hA.base.el,hA.base.gpr,hA.base.tag,hA.base.ls64,hA.base.tx,hA.base.nf,hA.base.ff⟩,
      hA.exclusive,hA.atomicop,hA.acqsc,hA.acqpc,hA.relsc⟩
  have hspe3 : Register.SPESampleInFlight.get t3.regs = false := by rw [fTag.1, f6.1]; exact hspe
  rcases occ_normal 1636 t3 with ⟨l2, t4, e8, f8⟩
  rcases physstat_normal l2 t4 with ⟨ps, t5, e9, f9⟩
  rcases occ_normal 1637 t5 with ⟨l3, t6, e10, f10⟩
  rcases S1EntryCalleesExtra.bool_normal l3 t6 with ⟨b3, t7, e11, f11⟩
  have G7 := frame_trans (frame_trans (frame_trans (frame_trans (frame_trans f6 fTag) f8) f9) f10) f11
  have e12 := physWrite ad n prepared t7 (Sail.BitVec.castWidth (m := 8 * n) v) (by rw [hpa]; exact hio)
  have preparedKind : AccessDescriptor_to_Access_kind prepared = AccessDescriptor_to_Access_kind acc := by
    rw [preparedEq]
    rfl
  have hfn : (ad.fault.statuscode != Fault.Fault_None) = false := by rw [hf]; rfl
  have hal := isAligned_gen a n hn ha
  have hai := allIn_gen a n hn ha s
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hsz := sizeOK_beq n hn
  have hwb : ((BEq.beq ad.memattrs.memtype MemType.MemType_Normal && (ad.memattrs.inner.attrs == MemAttr_WB)) &&
      (ad.memattrs.outer.attrs == MemAttr_WB)) = true := by
    rw [hmt, hin, hout]; decide
  refine ⟨ad, t1, { t7 with
      events := t7.events.push (.memWrite ad.paddress.address.toNat n (some ad.vaddress.toNat)
        (AccessDescriptor_to_Access_kind prepared) (some (Sail.BitVec.castWidth (m := 8 * n) v)) none)
      mem := wfold t7.mem ad.paddress.address.toNat n
        (fun j => (Sail.BitVec.castWidth (m := 8 * n) v).extractLsb' (8 * j) 8) },
    hQ, ?_, ?_, G7.1, ?_⟩
  rotate_left
  · show (t7.events.push _) = _
    rw [G7.2.2, hpa, preparedKind]
  · dsimp only
    rw [G7.2.1, hpa]
  cases tag : prepared.tagchecked
  all_goals simp only [tag, Bool.and_false, Bool.and_true, Bool.false_eq_true, ite_true, ite_false, Pure.pure, EStateM.pure,
    Bind.bind, EStateM.bind] at eTagIf
  case false =>
    cases eTagIf
    cases lse <;> cases tme <;>
    · unfold AArch64_MemSingle_set__1
      simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
        PreSail.assert, tag, hsz, hnn, e3, eM2, e4if, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai, hwb,
        hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.base.tx, IsFault, hfn, IsFault__2,
        CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
        ↓reduceIte, ite_self, bne_self_eq_false]
      done

  case true =>
    cases m7
    case false =>
      simp only [Bool.false_eq_true, ite_false, Pure.pure, EStateM.pure] at eTagIf
      cases eTagIf
      cases lse <;> cases tme <;>
      · unfold AArch64_MemSingle_set__1
        simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
          PreSail.assert, tag, hsz, hnn, e3, eM2, e4if, e5, e6, e7, e8, e9, e10, e11, e12, hal, hai, hwb,
          hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.base.tx, IsFault, hfn, IsFault__2,
          CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and, Bool.true_and,
          Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
          ↓reduceIte, ite_self, bne_self_eq_false]
        done
    case true =>
      have eTagT := eTag
      simp only [NativeMteTagCheck.checkedAccess, e7, Bool.true_and,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at eTagT
      simp only [tag, Bool.false_eq_true, ite_true, ite_false, Pure.pure, EStateM.pure, Bind.bind, EStateM.bind] at eTagT
      cases lse <;> cases tme <;>
      · unfold AArch64_MemSingle_set__1
        simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
          PreSail.assert, tag, hsz, hnn, e3, eM2, e4if, e5, e6, e7, eTagT, e8, e9, e10, e11, e12, hal, hai, hwb,
          hA'.exclusive, hA'.atomicop, hA'.acqsc, hA'.acqpc, hA'.relsc, hA'.base.tx, IsFault, hfn, IsFault__2,
          CreatePhysMemRetStatus, readReg, PreSail.readReg_apply, hspe3, Bool.and_false, Bool.false_and, Bool.true_and,
          Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_true,
          ↓reduceIte, ite_self, bne_self_eq_false]
        done

#print axioms store_natural
end ReleaseProfile.DefaultStores
