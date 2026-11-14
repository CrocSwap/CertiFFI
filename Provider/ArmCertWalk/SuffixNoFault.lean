import ArmCertWalk.WalkGuardFacts
import ArmCertWalk.SuffixNormal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Fault freedom of the ACTUAL source continuation from pure current data.
The output PA bound includes contiguous-bit offset semantics. Descriptor-slot
bounds alone do not establish it. No future callee answer is an input. -/
theorem suffix_no_fault_total (params : S1TTWParams) (config : PhysicalConfig)
    (va : BitVec 64) (acc : AccessDescriptor) (context : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (slot : FullAddress) (descriptor : BitVec 64)
    (fault : FaultRecord) (a64 s2 : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor)
    (next : TTWState) (level : Nat) (state : State)
    (d128 : params.d128 = 0#1) (tg : params.tgx = .TGx_4KB) (ips : params.ps = config.ips)
    (physical : PhysicalAt config state) (cache : state.regs.bank_Bool .__tlb_enabled = false)
    (positive : 1 ≤ level) (valid : level ≤ 3) (currentLevel : next.level = (level : Int))
    (nonsecure : next.baseaddress.paspace = .PAS_NonSecure)
    (noFault : fault.statuscode = .Fault_None) (ready : AFReady params .leaf descriptor)
    (noNT : next.level < 3 → blockFaultValue state.regs descriptor = false)
    (bound : (S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1)).address.toNat <
      2 ^ (effectiveBits config).toNat) :
    ∃ other,
      S1WalkSuffixSource.suffix params va .Regime_EL20 acc 64 context entry
        (aligned, slot, descriptor, .DescriptorType_Leaf, fault, a64, s2, skl, walkaddr, next) state =
        .ok (.ok (fault, walkaddr, next, descriptor)) other ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨oa, afterStage, stageCall, space, value, stageRegs, stageMem, stageEvents⟩ :=
    stage_canonical_total va next level state params d128 tg positive valid currentLevel
  have levels : 1 ≤ next.level ∧ next.level ≤ 3 := by omega
  have contiguousCall := contiguous_guard_false params.txsz next.level afterStage levels
  have blockCall (small : next.level < 3) :
      AArch64_BlocknTFaults 0#1 descriptor afterStage = .ok false afterStage := by
    rw [block_nt_fault_eq, stageRegs, noNT small]
  have amecCall : AArch64_S1AMECFault params next.baseaddress.paspace .Regime_EL20 descriptor afterStage =
      .ok false afterStage := by
    rw [nonsecure]
    exact amec_nonsecure_false params .Regime_EL20 descriptor afterStage d128
  have oaBound : oa.address.toNat < 2 ^ (effectiveBits config).toNat := by rw [value]; exact bound
  have rangeCall := oaOutOfRange_false config oa.address afterStage (physical.of_regs stageRegs) oaBound
  have cacheCall := S1CacheGuard.disabled descriptor fault (physicalPost afterStage)
    (by change afterStage.regs.bank_Bool .__tlb_enabled = false; rw [stageRegs]; exact cache)
  have afGuard : (((BitVec.join1 [BitVec.access descriptor 10]) == 0#1) && (params.ha == 0#1)) = false := by
    simpa using source_af_guard_false params descriptor ready
  have isLeaf : ((.DescriptorType_Leaf : DescriptorType) == .DescriptorType_Leaf) = true := by decide
  have noneNe : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  simp only [d128, tg] at stageCall
  refine ⟨physicalPost afterStage, ?_, stageRegs, stageMem, stageEvents⟩
  by_cases contiguous : next.contiguous = 1#1 <;> by_cases block : next.level < 3
  all_goals
    simp [S1WalkSuffixSource.suffix, d128, tg, ips, stageCall, contiguous, block, FINAL_LEVEL,
      contiguousCall, blockCall, amecCall, rangeCall, cacheCall, afGuard, isLeaf, noFault, noneNe,
      Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
      ExceptT.lift, EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
      MonadLift.monadLift, Sail.BitVec.length, ArmFull.assert, PreSail.assert]

#print axioms suffix_no_fault_total
end ArmCertWalk
