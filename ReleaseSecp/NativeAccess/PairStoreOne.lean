import NativeAccess.StpBytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace NativeAccess.PairStoreOne
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5 MemM1.MemWriteD6
open NativeAccess.Trace NativeAccess.Logical
attribute [local implicit_reducible] EStateM Arch.arch_ak

theorem store16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (s : Trace.State)
    (profile : AccessProfile) (pins : ProfileAt profile s) (lse : profile.lse2 = true)
    (plain : Plain acc) (fit : Read.Within16 a ((16 : Nat) : Int))
    (member : domain ⟨a,⟨acc,accessAligned a 16 true⟩,((16 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,accessAligned a 16 true⟩,((16 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,accessAligned a 16 true⟩,((16 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (pre : PreW acc s.regs) (hA : AccDWT acc) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 128) :
    ∃ (after : Trace.State) (calls : List WriteCall),
      Mem_set__2 a 16 acc true false value s = .ok () after ∧ WriteChain s calls after ∧
      calls.map WriteCall.request = [⟨offset,a,16,acc,accessAligned a 16 true,true⟩] ∧
      ∀ call ∈ calls, call.packet.ad.paddress.address = pa ∧
        (Sail.BitVec.castWidth call.packet.data : BitVec 128) = value := by
  have hn : SizeOK 16 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  rcases occ_normal 1646 s with ⟨l1,s1,e1,f1⟩
  rcases constraint_normal l1 s1 with ⟨c,s2,e2,f2⟩
  rcases occ_normal 1647 s2 with ⟨l2,s3,e3,f3⟩
  rcases S1EntryCalleesExtra.bool_normal l2 s3 with ⟨jp,s4,e4,f4⟩
  have F4 := frame_trans (frame_trans (frame_trans f1 f2) f3) f4
  have host4 : HostPins s4 := by
    rcases pins.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F4.1] <;> assumption
  have a4 : _get_SCTLR_EL2_Type_A (s4.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F4.1]; exact pins.alignment_disabled
  obtain ⟨s5,ef,ff⟩ : ∃ s5,
      ((if !(accessAligned a 16 true) then AArch64_UnalignedAccessFaults acc a (16 : Int)
        else pure false) : SailM Bool) s4 = .ok false s5 ∧ Frame s4 s5 := by
    cases h : accessAligned a 16 true with
    | false =>
      obtain ⟨u,eu,ru,mu,vu⟩ := plain_unaligned_allowed s4 host4 a4 acc plain a 16
      refine ⟨u,?_,ru,mu,vu⟩
      simp only [h,Bool.not_false,ite_true]
      exact eu
    | true => exact ⟨s4,by simp only [h,Bool.not_true,Bool.false_eq_true,ite_false]; rfl,
        rfl,rfl,rfl⟩
  simp only [Pure.pure] at ef
  have F5 := frame_trans F4 ff
  rcases littleEndian_of acc s hA pre s5 F5 with ⟨s6,e5,f5⟩
  have F6 := frame_trans F5 f5
  have ls6 : s6.regs.FeatureImpl[111] = true := by rw [F6.1,pins.lse2,lse]
  have e6 : HaveLSE2Ext () s6 = .ok true s6 := by rw [have_lse2,ls6]
  have hai := Store.allIn_of_fit a 16 hn fit s6
  let r : Access := ⟨offset,a,16,acc,accessAligned a 16 true,true⟩
  have current6 := current_s1_frame current F6.1 F6.2.1
  have access6 := access.of_regs F6.1
  have raw6 : RawImageAt spec.imageRows s6.mem := by rw [F6.2.1]; exact raw
  have none6 : NoUpdateRows {spec.params with haft := hostHAFT s6.regs} acc spec.imageRows = true := by
    rw [F6.1]; exact none
  rcases Current.write_within16 spec config rows mapping r s6 hn ls6 fit member data current6 access6
      (by rw [F6.1]; exact mode) (by rw [F6.1]; exact pre.aa64el0)
      (by rw [F6.1]; exact debug) (by rw [F6.1]; exact spe) hA
      (by rw [F6.1]; exact pre.tag) (by rw [F6.1]; exact dcache) pa mapped ram raw6 none6 value with
    ⟨packet,payload⟩
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hA.base.gpr]; rfl
  have address := StoreLoops.write_address spec config rows mapping r s6 member data current6 access6
    (by rw [F6.1]; exact mode) (by rw [F6.1]; exact pre.aa64el0)
    (by rw [F6.1]; exact debug) (by rw [F6.1]; exact spe) notFetch
    (by rw [F6.1]; exact dcache) pa mapped raw6 none6 packet
  have es := packet.run
  unfold Access.write at es
  rw [payload] at es
  have hsimd : (acc.acctype == AccessType.AccessType_ASIMD) = false := by rw [hA.base.gpr]; rfl
  have hsz : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by decide
  let call : WriteCall := ⟨r,s6,packet⟩
  refine ⟨packet.after,[call],?_,.cons call F6 (.nil ⟨rfl,rfl,rfl⟩),rfl,?_⟩
  · dsimp only [r] at es
    unfold accessAligned at ef es
    have sixteen : ((16 : Nat) : Int) = 16 := by decide
    simp only [sixteen,ite_true] at ef es hai
    unfold Mem_set__2
    simp only [sixteen]
    simp only [map_cast_checked,map_cast_same,bind_assoc,Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
      ArmFull.assert,PreSail.assert,hsz,e1,e2,e3,e4,ef,e5,e6,hai,es,hsimd,
      Sail.BitVec.castWidth_eq,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self]
  · intro c inside
    have same : c = call := List.mem_singleton.mp inside
    subst c
    refine ⟨address.1,?_⟩
    change (Sail.BitVec.castWidth packet.data : BitVec 128) = value
    rw [payload]
    exact Sail.BitVec.castWidth_eq _

#print axioms store16
end NativeAccess.PairStoreOne
