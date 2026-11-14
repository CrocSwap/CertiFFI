import NativeAccess.StpOne
import MemM1.MemPair8W
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace NativeAccess.PairStoreSplit
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5 MemM1.MemWriteD6 MemM1.MemWriteD7 MemM1.MemPair8R
open NativeAccess.Trace NativeAccess.PairSplit
attribute [local implicit_reducible] EStateM Arch.arch_ak

theorem store16 (a : BitVec 64) (h8 : a.toNat % 8 = 0) (h16 : a.toNat % 16 ≠ 0)
    (acc : AccessDescriptor) (s : Trace.State) (hLSE2 : s.regs.FeatureImpl[111] = true)
    (hA : AccDWT acc) (hP : PreW acc s.regs) (hspe : s.regs.bank_Bool .SPESampleInFlight = false)
    (domains : Fin 2 → QueryDomain) (specs : (j : Fin 2) → TopologyImageSpec (domains j))
    (configs : Fin 2 → AttributeConfig) (rows : Fin 2 → List PermissionRow)
    (mapping : Fin 2 → BitVec 64 → Option Nat) (pa : Fin 2 → BitVec 56)
    (member : ∀ j : Fin 2, domains j ⟨halfAddress a j,⟨acc,true⟩,((8 : Nat) : Int)⟩)
    (certs : ∀ j : Fin 2, S1AccessData (specs j) (configs j) (rows j) ⟨halfAddress a j,⟨acc,true⟩,((8 : Nat) : Int)⟩)
    (current : ∀ j : Fin 2, CurrentS1At (specs j) (configs j) (rows j) s)
    (access : ∀ j : Fin 2, CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
      ⟨halfAddress a j,⟨acc,true⟩,((8 : Nat) : Int)⟩ (certs j) s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs) (dcache : currentDCache s.regs = true)
    (mapped : ∀ j : Fin 2, mapping j (halfAddress a j) = some (pa j).toNat)
    (ram : ∀ j : Fin 2, NotMMIO (pa j))
    (raw : ∀ j : Fin 2, RawImageAt (specs j).imageRows s.mem)
    (none : ∀ j : Fin 2, NoUpdateRows {(specs j).params with haft := hostHAFT s.regs} acc (specs j).imageRows = true)
    (outside : ∀ j k : Fin 2, ∀ i < 8, ¬ (rowsFootprint (specs k).imageRows).byte ((pa j).toNat + i))
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
  rcases occ_normal 1646 s with ⟨l1, s1, e1, f1⟩
  rcases constraint_normal l1 s1 with ⟨c, s2, e2, f2⟩
  rcases occ_normal 1647 s2 with ⟨l2, s3, e3, f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp, s4, e4, f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  rcases littleEndian_of acc s hA hP s4 F4 with ⟨s5, e5, f5⟩
  have F5 := frame_trans F4 f5
  have e6 := MemM1.MemWriteD5.lse2_on s5 (by rw [F5.1]; exact hLSE2)
  have hai := allIn16_false a h8 h16 s5
  rcases occ_normal 1650 s5 with ⟨l3, s6, e7, f6⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l3 s6 with ⟨b2, s7, e8, f7⟩
  rcases occ_normal 1651 s7 with ⟨l4, s8, e9, f8⟩
  rcases bits_normal (Sail.Int.toNatChecked (((Sail.Int.toNatChecked (Int.ediv (((16 : Nat) : Int)) 2) : Nat) : Int) * 8)) l4 s8 with ⟨b3, s9, e10, f9⟩
  have F9 := frame_trans (frame_trans (frame_trans (frame_trans F5 f6) f7) f8) f9
  obtain ⟨rc3, e11⟩ : ∃ b, HaveLRCPC3Ext () s9 = .ok b s9 := ⟨_, rfl⟩
  have hn8 : SizeOK 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.base.gpr]; rfl
  let j0 : Fin 2 := ⟨0,by decide⟩
  let r0 : Access := ⟨0,a,8,acc,true,false⟩
  have current0 := current_s1_frame (current j0) F9.1 F9.2.1
  have access0 := (access j0).of_regs F9.1
  have raw0 : RawImageAt (specs j0).imageRows s9.mem := by
    rw [F9.2.1]; exact raw j0
  have none0 : NoUpdateRows {(specs j0).params with haft := hostHAFT s9.regs} acc (specs j0).imageRows = true := by
    rw [F9.1]; exact none j0
  rcases Current.write_natural (specs j0) (configs j0) (rows j0) (mapping j0) r0 s9 hn8 h8
      (member j0) (certs j0) current0 access0
      (by rw [F9.1]; exact mode) (by rw [F9.1]; exact hP.aa64el0)
      (by rw [F9.1]; exact debug) (by rw [F9.1]; exact hspe) hA
      (by rw [F9.1]; exact hP.tag) (by rw [F9.1]; exact dcache)
      (pa j0) (mapped j0) (ram j0) raw0 none0 (Bytes.low64 v) with ⟨p0,value0⟩
  have physical0 := StoreLoops.write_address (specs j0) (configs j0) (rows j0) (mapping j0) r0 s9
      (member j0) (certs j0) current0 access0
      (by rw [F9.1]; exact mode) (by rw [F9.1]; exact hP.aa64el0)
      (by rw [F9.1]; exact debug) (by rw [F9.1]; exact hspe) notFetch
      (by rw [F9.1]; exact dcache) (pa j0) (mapped j0) raw0 none0 p0
  let x := p0.after
  have rx : x.regs = s.regs := p0.registers.trans F9.1
  have preserved : ∀ k : Fin 2, CurrentS1At (specs k) (configs k) (rows k) x ∧
      RawImageAt (specs k).imageRows x.mem := by
    intro k
    apply StoreLoops.current_after_packet (current_s1_frame (current k) F9.1 F9.2.1)
      (by rw [F9.2.1]; exact raw k) p0
    intro i hi
    rw [physical0.1]
    exact outside j0 k i hi
  let j1 : Fin 2 := ⟨1,by decide⟩
  let r1 : Access := ⟨8,(BitVec.addInt a ((8 : Nat) : Int)),8,acc,true,false⟩
  have current1 := (preserved j1).1
  have access1 := (access j1).of_regs rx
  have raw1 : RawImageAt (specs j1).imageRows x.mem := by
    exact (preserved j1).2
  have none1 : NoUpdateRows {(specs j1).params with haft := hostHAFT x.regs} acc (specs j1).imageRows = true := by
    rw [rx]; exact none j1
  rcases Current.write_natural (specs j1) (configs j1) (rows j1) (mapping j1) r1 x hn8 hb8
      (member j1) (certs j1) current1 access1
      (by rw [rx]; exact mode) (by rw [rx]; exact hP.aa64el0)
      (by rw [rx]; exact debug) (by rw [rx]; exact hspe) hA
      (by rw [rx]; exact hP.tag) (by rw [rx]; exact dcache)
      (pa j1) (mapped j1) (ram j1) raw1 none1 (Bytes.high64 v) with ⟨p1,value1⟩
  have physical1 := StoreLoops.write_address (specs j1) (configs j1) (rows j1) (mapping j1) r1 x
      (member j1) (certs j1) current1 access1
      (by rw [rx]; exact mode) (by rw [rx]; exact hP.aa64el0)
      (by rw [rx]; exact debug) (by rw [rx]; exact hspe) notFetch
      (by rw [rx]; exact dcache) (pa j1) (mapped j1) raw1 none1 p1
  let t := p1.after
  have rt : t.regs = s.regs := p1.registers.trans rx
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
  refine ⟨t,[call0,call1],?_,.cons call0 F9 (.cons call1 ⟨rfl,rfl,rfl⟩ (.nil ⟨rfl,rfl,rfl⟩)),rfl,?_⟩
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
    · refine ⟨j0,rfl,physical0.1,?_⟩
      change (Sail.BitVec.castWidth p0.data : BitVec 64) = _
      rw [value0]
      exact Sail.BitVec.castWidth_eq _
    · have same : call = call1 := List.mem_singleton.mp inside
      subst call
      refine ⟨j1,rfl,physical1.1,?_⟩
      change (Sail.BitVec.castWidth p1.data : BitVec 64) = _
      rw [value1]
      exact Sail.BitVec.castWidth_eq _

#print axioms store16
end NativeAccess.PairStoreSplit
