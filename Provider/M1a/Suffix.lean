import M1a.Loop20
import Walk.S1WalkSuffix
import Walk.S1CacheGuard
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a

theorem amec_eq (wp : S1TTWParams) (pas : PASpace) (regime : Regime) (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) (s : State) :
    AArch64_S1AMECFault wp pas regime d s = .ok (S1WalkChecks.amec wp pas regime d) s := by
  simp [AArch64_S1AMECFault, S1WalkChecks.amec, S1DecodeFacts.bit, hD128, ArmFull.assert,
    PreSail.assert, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

/-- The post-loop suffix of the actual S1Walk at a normal leaf: no check fires and
    it returns (fault, walkaddr, walkstate, descriptor) unchanged. -/
theorem suffix_result (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (slot : FullAddress) (d : BitVec 64) (f : FaultRecord)
    (a64 mro : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor) (w : TTWState)
    (s : State)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB)
    (hl : w.level = 3) (hc : w.contiguous = 0#1)
    (hpas : w.baseaddress.paspace = .PAS_NonSecure)
    (hf : f.statuscode = .Fault_None)
    (hAF : BitVec.join1 [BitVec.access d 10] = 1#1)
    (hOA : (!is_zero_subrange (S1StageOA.address va w).address 55
      (S2PhysicalSizeFrame.value wp.ps)) = false)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false) :
    ∃ t : State,
      S1WalkSuffixSource.suffix wp va regime acc 64 ctx entry
        (aligned, slot, d, .DescriptorType_Leaf, f, a64, mro, skl, walkaddr, w) s =
        .ok (.ok (f, walkaddr, w, d)) t ∧ t.regs = s.regs ∧ t.mem = s.mem := by
  rcases S1StageOA.total va w s (by omega) with ⟨t1, hoa, hf1⟩
  rcases S2OAFrame.total (S1StageOA.address va w).address wp.ps t1 (by rw [hf1.1]; exact hPA) with
    ⟨t2, hrange, hr2, hm2, _⟩
  have hc2 : t2.regs.bank_Bool .__tlb_enabled = false := by rw [hr2, hf1.1]; exact hCache
  have hguard := S1CacheGuard.disabled d f t2 hc2
  have hamec := amec_eq wp .PAS_NonSecure regime d hd t1
  have hAF0 : ¬ (BitVec.join1 [BitVec.access d 10] = 0#1) := by rw [hAF]; simp
  have hR : (PASpace.PAS_NonSecure == PASpace.PAS_Realm) = false := by decide
  have hFin : ¬ ((3 : Int) < FINAL_LEVEL) := by decide
  have hNo : ((Fault.Fault_None : Fault) != Fault.Fault_None) = false := by decide
  refine ⟨t2, ?_, hr2.trans hf1.1, hm2.trans hf1.2.1⟩
  unfold S1WalkSuffixSource.suffix
  simp only [hd, htg, hl, hc]
  simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, ExceptT.lift,
    Pure.pure, EStateM.bind, EStateM.pure, EStateM.map, Functor.map, liftM,
    MonadLiftT.monadLift, MonadLift.monadLift, hoa, hrange, hOA, hguard, hf, hAF0,
    hamec, S1WalkChecks.amec, hpas, hR, hFin, hNo, hd, ArmFull.assert, PreSail.assert]

#print axioms suffix_result
end ArmCert.Eval.M1a
