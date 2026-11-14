import PairDefault236.ByteLoops
import NativeAccess.LdpBytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open NativeAccess
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
namespace PairDefault236.PairOne
variable {catalogue : NativeMteTagCheck.ControlCatalogue}
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open PairDefault236.Trace
open TranslateSpan.DefaultAccessTrace NativeMteTagCheck
open NativeAccess.Trace (Access)
attribute [local implicit_reducible] EStateM Arch.arch_ak

def pairAligned (a : BitVec 64) : Bool :=
  IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int)

theorem read16 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (offset : Nat) (a : BitVec 64) (acc : AccessDescriptor) (high : Bool) (s : Trace.State)
    (profile : AccessProfile) (pins : ProfileAt profile s) (lse : profile.lse2 = true)
    (plain : Plain acc) (natural : a.toNat % 16 = 0) (fit : NativeMte2.Read.Within16 a 16)
    (m : Current.Consumer) (current : Current.At spec config rows mapping m catalogue s)
    (statusRows : TagStatusRows s (s.choiceOcc.getD 1354 0) 1)
    (shape : DataShape false acc) (hA : AccDR2 acc) (el : acc.el = EL0)
    (permitted : ∀ prepared, DataShape false prepared → m.permitted a prepared (pairAligned a) (16 : Int))
    (pa : BitVec 56) (mapped : mapping a = some pa.toNat) (ram : NotMMIO pa)
    (value : BitVec 128) (bytes : ∀ i < 16, s.mem[pa.toNat + i]? = some (value.extractLsb' (8 * i) 8)) :
    ∃ (after : Trace.State) (calls : List ReadCall),
      Mem_read__2 a 16 acc true high s = .ok value after ∧ ReadChain s calls after ∧
      calls.map ReadCall.request = [⟨offset,a,16,acc,pairAligned a,true⟩] := by
  rcases Control.occ_normal 1640 s with ⟨l1, s1, e1, f1⟩
  obtain ⟨c, e2⟩ := constraint_ok l1 s1
  rcases Control.occ_normal 1641 s1 with ⟨l2, s2, e3, f2⟩
  rcases Control.bits_normal (Sail.Int.toNatChecked (((16 : Nat) : Int) * 8)) l2 s2 with ⟨b1, s3, e4, f3⟩
  have F3 := NativeMteTagCheck.StatusTrace.frame_trans (NativeMteTagCheck.StatusTrace.frame_trans f1 f2) f3
  have host3 : NativeAccess.HostPins s3 := by
    rcases pins.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [F3.1] <;> assumption
  have a3 : _get_SCTLR_EL2_Type_A (s3.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1 := by
    rw [F3.1]; exact pins.alignment_disabled
  obtain ⟨s4, ef, ff⟩ : ∃ s4,
      ((if !(IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int)) then AArch64_UnalignedAccessFaults acc a ((16 : Nat) : Int)
        else pure false) : SailM Bool) s3 = .ok false s4 ∧ NativeMteTagCheck.StatusTrace.TraceFrame s3 s4 := by
    cases h : IsAligned__1 a ((Sail.Int.toNatChecked (Int.ediv ((16 : Nat) : Int) 2)) : Int) with
    | false =>
      obtain ⟨u, eu, ru, mu, vu, du⟩ := Control.plain_unaligned_allowed s3 host3 a3 acc plain a ((16 : Nat) : Int)
      refine ⟨u, ?_, ru, mu, vu,du⟩
      simp only [h, Bool.not_false, ite_true]
      exact eu
    | true => exact ⟨s3, by simp only [h, Bool.not_true, Bool.false_eq_true, ite_false]; rfl,
        rfl,rfl,rfl,choice_delta_refl _⟩
  simp only [Pure.pure] at ef
  have F4 := NativeMteTagCheck.StatusTrace.frame_trans F3 ff
  have ls4 : s4.regs.FeatureImpl[111] = true := by rw [F4.1, pins.lse2, lse]
  have e5 : HaveLSE2Ext () s4 = .ok true s4 := by rw [have_lse2, ls4]
  have hai := NativeMte2.Read.allIn16_of_fit a fit s4
  obtain ⟨packet,payload,physical⟩ := Current.read16_natural (current.frame (NativeMteTagCheck.StatusTrace.to_frame F4))
    offset a acc (pairAligned a) true natural shape hA el permitted
    (tag_status_transport F4.2.2.2 (tag_status_of_rows s s _ _ 0 statusRows rfl (by omega) (by omega))) pa mapped ram value
    (by intro i hi; rw [F4.2.1]; exact bytes i hi)
  have e6 := packet.run
  unfold Access.read at e6
  dsimp only [pairAligned] at e6
  rw [payload] at e6
  have hPt : PostRegs packet.after.regs := by rw [packet.registers,F4.1]; exact current.post
  rcases Control.be_false packet.after hPt.el0 hPt.nrw hPt.noRME hPt.vhe hPt.aa64el0
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
end PairDefault236.PairOne
