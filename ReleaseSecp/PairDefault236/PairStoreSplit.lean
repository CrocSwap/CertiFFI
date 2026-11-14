import PairDefault236.ByteLoops
import NativeAccess.StpOne
import PairDefault236.PairSplit
import MemM1.MemPair8W
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open NativeAccess
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace PairDefault236.PairStoreSplit
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7 MemM1.MemPair8R
open PairDefault236.Trace
open TranslateSpan.DefaultAccessTrace NativeMteTagCheck
open NativeAccess.Trace (Access)
open PairDefault236.PairSplit
attribute [local implicit_reducible] EStateM Arch.arch_ak

theorem store16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (s : Trace.State) (hLSE2 : s.regs.FeatureImpl[111] = true)
    (m : Current.Consumer) (current : Current.At spec config rows mapping m catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 2)
    (shape : DataShape true acc) (hA : AccDWT acc) (pa : Fin 2 → BitVec 56)
    (permitted : ∀ prepared, DataShape true prepared → ∀ j : Fin 2, m.permitted (halfAddress a j) prepared true (8 : Int))
    (mapped : ∀ j : Fin 2, mapping (halfAddress a j) = some (pa j).toNat)
    (ram : ∀ j : Fin 2, NotMMIO (pa j))
    (outside : ∀ j : Fin 2, ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte ((pa j).toNat + i))
    (v : BitVec 128) :
    ∃ (after : Trace.State) (calls : List WriteCall), Mem_set__1 a 16 acc true v s = .ok () after ∧
      WriteChain s calls after ∧ calls.map WriteCall.request =
        [⟨0,a,8,acc,true,false⟩,⟨8,BitVec.addInt a ((8 : Nat) : Int),8,acc,true,false⟩] ∧
      ∀ call ∈ calls, ∃ j : Fin 2,
        call.request = ⟨8 * j.val,halfAddress a j,8,acc,true,false⟩ ∧
        call.packet.ad.paddress.address = pa j ∧
        (Sail.BitVec.castWidth call.packet.data : BitVec 64) = halfValue v j := by
  have hb8 : (BitVec.addInt a ((8 : Nat) : Int)).toNat % 8 = 0 := by
    rw [addInt8]; simp [BitVec.toNat_add]; omega
  rcases Control.occ_normal 1646 s with ⟨l1, s1, e1, f1⟩
  rcases Control.constraint_normal l1 s1 with ⟨c, s2, e2, f2⟩
  rcases Control.occ_normal 1647 s2 with ⟨l2, s3, e3, f3⟩
  rcases Control.bool_normal l2 s3 with ⟨jp, s4, e4, f4⟩
  have F4 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans f1 f2) f3) f4
  rcases Control.littleEndian_of acc hA current.post s4 F4 with ⟨s5, e5, f5⟩
  have F5 := NativeMteTagCheck.StatusTrace.frame_trans F4 f5
  have e6 := MemM1.MemWriteD5.lse2_on s5 (by rw [F5.1]; exact hLSE2)
  have hai := allIn16_false a h8 h16 s5
  rcases Control.occ_normal 1650 s5 with ⟨l3, s6, e7, f6⟩
  rcases Control.bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s6 with ⟨b2, s7, e8, f7⟩
  rcases Control.occ_normal 1651 s7 with ⟨l4, s8, e9, f8⟩
  rcases Control.bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s8 with ⟨b3, s9, e10, f9⟩
  have F9 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans F5 f6) f7) f8) f9
  obtain ⟨rc3, e11⟩ : ∃ b, HaveLRCPC3Ext () s9 = .ok b s9 := ⟨_, rfl⟩
  have hn8 : SizeOK 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  let j0 : Fin 2 := ⟨0,by decide⟩
  let r0 : Access := ⟨0,a,8,acc,true,false⟩
  have current0 := current.frame (NativeMteTagCheck.StatusTrace.to_frame F9)
  obtain ⟨p0,value0,physical0⟩ := Current.store_natural current0 0 a 8 hn8 acc true false h8 shape hA shape.el
    (fun prepared sh => permitted prepared sh j0)
    (tag_status_transport F9.2.2.2 (tag_status_of_rows s s _ _ 0 statusRows rfl (by omega) (by omega))) (pa j0) (mapped j0) (ram j0) (Bytes.low64 v)
  let x := p0.after
  have current1 := current0.after_write p0 (by
    intro i hi
    rw [physical0]
    exact outside j0 i hi)
  let j1 : Fin 2 := ⟨1,by decide⟩
  let r1 : Access := ⟨8,(BitVec.addInt a ((8 : Nat) : Int)),8,acc,true,false⟩
  obtain ⟨p1,value1,physical1⟩ := Current.store_natural current1 8 (BitVec.addInt a ((8 : Nat) : Int)) 8 hn8 acc true false hb8 shape hA shape.el
    (fun prepared sh => permitted prepared sh j1)
    (tag_status_of_rows s x _ _ p0.draws statusRows
      (choice_delta_trans F9.2.2.2 p0.choice).1
      (by simpa using (choice_delta_trans F9.2.2.2 p0.choice).2)
      (by have := p0.drawBound; omega)) (pa j1) (mapped j1) (ram j1) (Bytes.high64 v)
  let t := p1.after
  have ex := p0.run
  have ey := p1.run
  unfold Access.write at ex ey
  rw [value0] at ex
  rw [value1] at ey
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 a h8
  have hsimd : (BEq.beq acc.acctype AccessType.AccessType_ASIMD) = false := by rw [hA.base.gpr]; rfl
  have ex' : AArch64_MemSingle_set__1 a (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false
      (v.extractLsb' 0 64) s9 = .ok () x := by
    change AArch64_MemSingle_set__1 a 8 acc true false (v.extractLsb' 0 64) s9 = .ok () x
    simpa only [r0,Bytes.low64,Sail.BitVec.extractLsb,BitVec.extractLsb,Sail.BitVec.castWidth_eq] using ex
  have ey' : AArch64_MemSingle_set__1 (BitVec.addInt a ((8 : Nat) : Int))
      (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false
      (v.extractLsb' 64 64) x = .ok () t := by
    change AArch64_MemSingle_set__1 (BitVec.addInt a ((8 : Nat) : Int)) 8 acc true false (v.extractLsb' 64 64) x = .ok () t
    simpa only [r1,Bytes.high64,Sail.BitVec.extractLsb,BitVec.extractLsb,Sail.BitVec.castWidth_eq] using ey
  let call0 : WriteCall := ⟨r0,s9,p0⟩
  let call1 : WriteCall := ⟨r1,x,p1⟩
  refine ⟨t,[call0,call1],?_,.cons call0 F9 (.cons call1 ⟨rfl,rfl,rfl,choice_delta_refl _⟩ (.nil ⟨rfl,rfl,rfl,choice_delta_refl _⟩)),rfl,?_⟩
  · unfold Mem_set__1 Mem_set__2
    simp (config := { decide := true }) only [Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,
      EStateM.pure,ArmFull.assert,PreSail.assert,hhalf,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,
      hal,hai,hsimd,Sail.BitVec.castWidth_eq,Bool.and_false,Bool.false_and,Bool.or_false,
      Bool.false_or,Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,
      ↓reduceIte,ite_self]
    erw [ex']
    simp only []
    erw [ey']
  · intro call inside
    rcases List.mem_cons.mp inside with rfl | inside
    · refine ⟨j0,rfl,physical0,?_⟩
      change (Sail.BitVec.castWidth p0.data : BitVec 64) = _
      rw [value0]
      exact Sail.BitVec.castWidth_eq _
    · have same : call = call1 := List.mem_singleton.mp inside
      subst call
      refine ⟨j1,rfl,physical1,?_⟩
      change (Sail.BitVec.castWidth p1.data : BitVec 64) = _
      rw [value1]
      exact Sail.BitVec.castWidth_eq _

#print axioms store16
end PairDefault236.PairStoreSplit
