import PairDefault236.ByteLoops
import NativeAccess.LdpOne
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open NativeAccess
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace PairDefault236.PairSplit
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2 MemM1.MemPair8R
open PairDefault236.Trace
open TranslateSpan.DefaultAccessTrace NativeMteTagCheck
open NativeAccess.Trace (Access)
attribute [local implicit_reducible] EStateM Arch.arch_ak

def halfAddress (a : BitVec 64) (j : Fin 2) : BitVec 64 :=
  if j.val = 0 then a else BitVec.addInt a ((8 : Nat) : Int)
def halfValue (data : BitVec 128) (j : Fin 2) : BitVec 64 :=
  if j.val = 0 then Bytes.low64 data else Bytes.high64 data

theorem read16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (s : Trace.State) (hLSE2 : s.regs.FeatureImpl[111] = true)
    (m : Current.Consumer) (current : Current.At spec config rows mapping m catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 2)
    (shape : DataShape false acc) (hA : AccDR2 acc) (el : acc.el = EL0)
    (pa : Fin 2 → BitVec 56)
    (permitted : ∀ prepared, DataShape false prepared → ∀ j : Fin 2, m.permitted (halfAddress a j) prepared true (8 : Int))
    (mapped : ∀ j : Fin 2, mapping (halfAddress a j) = some (pa j).toNat)
    (ram : ∀ j : Fin 2, NotMMIO (pa j))
    (data : BitVec 128)
    (bytes : ∀ j : Fin 2, ∀ i < 8, s.mem[(pa j).toNat + i]? = some ((halfValue data j).extractLsb' (8 * i) 8)) :
    ∃ (after : Trace.State) (calls : List ReadCall), Mem_read__1 a 16 acc true s = .ok data after ∧
      ReadChain s calls after ∧ calls.map ReadCall.request =
        [⟨0,a,8,acc,true,false⟩,⟨8,BitVec.addInt a ((8 : Nat) : Int),8,acc,true,false⟩] := by
  have hb8 : (BitVec.addInt a ((8 : Nat) : Int)).toNat % 8 = 0 := by
    rw [addInt8]; simp [BitVec.toNat_add]; omega
  rcases Control.occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases Control.occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases Control.bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans f1 f2) f3
  have e5 := lse2_on s3 (by rw [F3.1]; exact hLSE2)
  have hai := allIn16_false a h8 h16 s3
  rcases Control.occ_normal 1644 s3 with ⟨l3, s4, e6, f4⟩
  rcases Control.bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s4 with ⟨b2, s5, e7, f5⟩
  rcases Control.occ_normal 1645 s5 with ⟨l4, s6, e8, f6⟩
  rcases Control.bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s6 with ⟨b3, s7, e9, f7⟩
  have F7 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans F3 f4) f5) f6) f7
  obtain ⟨rc3, e10⟩ : ∃ b, HaveLRCPC3Ext () s7 = .ok b s7 := ⟨_, rfl⟩
  let j0 : Fin 2 := ⟨0,by decide⟩
  obtain ⟨p0,value0,pa0⟩ := Current.read8_natural (current.frame (NativeMteTagCheck.StatusTrace.to_frame F7)) 0 a acc true false h8
    shape hA el (fun prepared sh => permitted prepared sh j0)
    (tag_status_transport F7.2.2.2 (tag_status_of_rows s s _ _ 0 statusRows rfl (by omega) (by omega))) (pa j0) (mapped j0) (ram j0) (Bytes.low64 data)
    (by intro i hi; rw [F7.2.1]; exact bytes j0 i hi)
  let x := p0.after
  have rx : x.regs = s.regs := p0.registers.trans F7.1
  have mx : x.mem = s.mem := p0.memory.trans F7.2.1
  let j1 : Fin 2 := ⟨1,by decide⟩
  obtain ⟨p1,value1,pa1⟩ := Current.read8_natural (current.of_regs_mem rx mx) 8
    (BitVec.addInt a ((8 : Nat) : Int)) acc true false hb8 shape hA el
    (fun prepared sh => permitted prepared sh j1)
    (tag_status_of_rows s x _ _ p0.draws statusRows
      (choice_delta_trans F7.2.2.2 p0.choice).1
      (by simpa using (choice_delta_trans F7.2.2.2 p0.choice).2)
      (by have := p0.drawBound; omega)) (pa j1) (mapped j1) (ram j1) (Bytes.high64 data)
    (by intro i hi; rw [mx]; exact bytes j1 i hi)
  let y := p1.after
  have ry : y.regs = s.regs := p1.registers.trans rx
  have my : y.mem = s.mem := p1.memory.trans mx
  have ex := p0.run
  have ey := p1.run
  unfold Access.read at ex ey
  rw [value0] at ex
  rw [value1] at ey
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have ex' : AArch64_MemSingle_read__1 a (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false s7
      = .ok (data.extractLsb' 0 64) x := by
    change AArch64_MemSingle_read__1 a 8 acc true false s7 = .ok (data.extractLsb' 0 64) x
    simpa only [Bytes.low64,Sail.BitVec.extractLsb,BitVec.extractLsb,Sail.BitVec.castWidth_eq] using ex
  have ey' : AArch64_MemSingle_read__1 (BitVec.addInt a ((8 : Nat) : Int))
      (Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2)) acc true false x
      = .ok (data.extractLsb' 64 64) y := by
    change AArch64_MemSingle_read__1 (BitVec.addInt a ((8 : Nat) : Int)) 8 acc true false x =
      .ok (data.extractLsb' 64 64) y
    simpa only [Bytes.high64,Sail.BitVec.extractLsb,BitVec.extractLsb,Sail.BitVec.castWidth_eq] using ey
  have hPy : PostRegs y.regs := by rw [ry]; exact current.post
  rcases Control.be_false y hPy.el0 hPy.nrw hPy.noRME hPy.vhe hPy.aa64el0 hPy.ns hPy.e2h
      hPy.tge hPy.e0e with ⟨t,e11,f11⟩
  have hhalf : Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) = 8 := by decide
  have hal := MemM1.MemReadD.isAligned8 a h8
  have hsz2 : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by decide
  have hh8 : (((((8 : Nat) == 1 || (8 : Nat) == 2) || (8 : Nat) == 4) || (8 : Nat) == 8)) = true := by decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  let call0 : ReadCall := ⟨⟨0,a,8,acc,true,false⟩,s7,p0⟩
  let call1 : ReadCall := ⟨⟨8,BitVec.addInt a ((8 : Nat) : Int),8,acc,true,false⟩,x,p1⟩
  refine ⟨t,[call0,call1],?_,.cons call0 F7 (.cons call1 ⟨rfl,rfl,rfl,choice_delta_refl _⟩ (.nil f11)),rfl⟩
  unfold Mem_read__1 Mem_read__2 AArch64_MemSingle_read
  simp only [Functor.map, EStateM.map, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ArmFull.assert,
    PreSail.assert, hsz2, hh8, hhalf, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ex', ey', hA.gpr, e11, hal,
    hai, hga, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, Bool.and_true, Bool.true_and, ↓reduceIte, ite_self,
    Sail.BitVec.castWidth_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp (disch := decide) only [cw_toNat, BitVec.append_eq]
  rw [← join_toNat data, BitVec.toNat_append, BitVec.toNat_append]
  have hw : Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int)) * 8
      = 64 := by decide
  rw [hw]
  rfl

#print axioms read16
end PairDefault236.PairSplit
