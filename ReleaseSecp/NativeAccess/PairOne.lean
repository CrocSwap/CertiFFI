import NativeAccess.LdpBytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace NativeAccess.PairOne
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open NativeAccess.Trace
attribute [local implicit_reducible] EStateM Arch.arch_ak

def pairAligned (a : BitVec 64) : Bool :=
  IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int)

theorem read16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (high : Bool) (s : Trace.State)
    (profile : AccessProfile) (pins : ProfileAt profile s) (lse : profile.lse2 = true)
    (plain : Plain acc) (fit : Read.Within16 a 16)
    (member : domain ⟨a,⟨acc,pairAligned a⟩,((16 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨a,⟨acc,pairAligned a⟩,((16 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping
      ⟨a,⟨acc,pairAligned a⟩,((16 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (debug : ExistingE11DebugAt s.regs)
    (post : PostRegs2 s.regs) (hA : AccDR2 acc) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (raw : RawImageAt spec.imageRows s.mem)
    (none : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (value : BitVec 128) (bytes : ∀ i < 16, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ (after : Trace.State) (calls : List ReadCall),
      Mem_read__2 a 16 acc true high s = .ok value after ∧ ReadChain s calls after ∧
      calls.map ReadCall.request = [⟨offset,a,16,acc,pairAligned a,true⟩] := by
  rcases occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := frame_trans (frame_trans f1 f2) f3
  have host3 : HostPins s3 := by
    rcases pins.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F3.1] <;> assumption
  have a3 : _get_SCTLR_EL2_Type_A (s3.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F3.1]; exact pins.alignment_disabled
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
  have ls4 : s4.regs.FeatureImpl[111] = true := by rw [F4.1, pins.lse2, lse]
  have e5 : HaveLSE2Ext () s4 = .ok true s4 := by rw [have_lse2, ls4]
  have hai := Read.allIn16_of_fit a fit s4
  rcases Current.read16_within16 spec config rows mapping offset a acc (pairAligned a) true s4 ls4 fit
      member data (current_s1_frame current F4.1 F4.2.1) (access.of_regs F4.1)
      (by rw [F4.1]; exact mode) (by rw [F4.1]; exact debug)
      (by rw [F4.1]; exact post) hA (by rw [F4.1]; exact dcache) pa mapped ram
      (by rw [F4.2.1]; exact raw) (by rw [F4.1]; exact none) value
      (by intro i hi; rw [F4.2.1]; exact bytes i hi) with ⟨packet,payload⟩
  have e6 := packet.run
  unfold Access.read at e6
  dsimp only [pairAligned] at e6
  rw [payload] at e6
  have hPt : PostRegs packet.after.regs := by rw [packet.registers,F4.1]; exact post.post
  rcases MemM1.MemReadDBE.be_false packet.after hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0
      hPt.ns hPt.e2h hPt.tge hPt.e0e with ⟨after,e7,f7⟩
  let call : ReadCall := ⟨⟨offset,a,16,acc,pairAligned a,true⟩,s4,packet⟩
  refine ⟨after,[call],?_,.cons call F4 (.nil f7),rfl⟩
  have hsz : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by decide
  have hga : (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false := rfl
  unfold Mem_read__2
  simp only [Functor.map,EStateM.map,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure,
    ArmFull.assert,PreSail.assert,hsz,e1,e2,e3,e4,ef,e5,hai,e6,hA.gpr,hga,e7,
    Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,Bool.and_true,Bool.true_and,↓reduceIte,ite_self,Sail.BitVec.castWidth_eq]

#print axioms read16
end NativeAccess.PairOne
