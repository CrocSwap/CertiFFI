import PipeLean_D234_SecpMul_c16.DitBodyExit
import DitShim243.EpiABI
import DitShim243.PreABI
import PipeLean_D234_SecpMul_c16.DitBodyState
import DitShim243.BodyEntry
import DitShim243.Prologue
import TranslateSpan.DefaultFiniteRows
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts NativeMteTagCheck ReleaseProfile ArmCertValue ArmCertPipe
open CertiFFI.Prog.Generic.ModelRunView DitShim243
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMul_c16.Shim32Run

section Entry
variable (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (gt : CheckedTopology.check raw (Deployment.addresses EntryBinding.plan base entry start imm (BitVec.ofNat 64 pins.sp)) 4 = true)
    (rt : CheckedTopology.check raw (SecpRawDeployment.addresses EntryBinding.plan base entry) 4 = true)
    (info : Initial.Info EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0))
      start imm 157 pins (DefaultState.capacity entry + 2) entry catalogue gt rt)

include info

theorem of_initial :
    (∀ k, k < 169 → modelStep real (stateAt real entry k) = .ok () (stateAt real entry (k+1))) ∧
    (stateAt real entry 169).regs._PC = entryGPR entry 30 ∧
    (stateAt real entry 169).regs.gpr[30] = entry.regs.gpr[30] ∧
    (stateAt real entry 169).regs.SP_EL0 = entry.regs.SP_EL0 ∧
    (stateAt real entry 169).regs.PSTATE.DIT = entry.regs.PSTATE.DIT ∧
    (∀ j, 5 ≤ j → j ≤ 167 → (stateAt real entry j).regs.PSTATE.DIT = 1#1) ∧
    (∀ pa, pa ∉ outputBytes EntryBinding.plan mapping entry → ¬ RtShim2.ShimMem.slotBytes pins mapping pa →
      (stateAt real entry 169).mem[pa]? = entry.mem[pa]?) ∧
    (∃ used, ChoiceDelta entry (stateAt real entry 169) used ∧ used ≤ DefaultState.capacity entry+2) ∧
    ShimABI.Fields entry (stateAt real entry 169) ∧
    (∀ i : Fin 31, 18 ≤ i.val → (stateAt real entry 169).regs.gpr[i.val] = entry.regs.gpr[i.val]) ∧
    (∀ pa : Nat, (stateAt real entry 169).mem[pa]? = (stateAt real entry 165).mem[pa]?) ∧
    (∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → (stateAt real entry 7).regs.gpr[i.val] = entry.regs.gpr[i.val]) ∧
    ArmCertMemPipe.TLSFrame.tp (stateAt real entry 7) = ArmCertMemPipe.TLSFrame.tp entry := by
  obtain ⟨pre,savedDIT⟩ := Prologue.of_initial real EntryBinding.plan raw config rows mapping base _ start imm 157 pins (DefaultState.capacity entry+2) entry catalogue gt rt info
  obtain ⟨returned,sp31,slot31,ctl31,⟨used,delta,usedBound⟩,dit31⟩ := DitBodyExit.of_pre real raw config rows mapping base start imm pins entry catalogue gt rt info pre
  have aligned := Geometry.whole_aligned start (InitialCheck.rawPC EntryBinding.plan) 157 base (entryGPR entry 30) info.metadata.startAligned info.metadata.bodyAligned
  have offPre' : ∀ j, j ≤ 6 → InitialCheck.runOffset EntryBinding.plan start 157 base entry j = Geometry.shimPC start j := by
    intro j hj; exact Geometry.whole_prefix start (InitialCheck.rawPC EntryBinding.plan) 157 j base (entryGPR entry 30) hj
  have offPost' : ∀ j, 165 ≤ j → j ≤ 168 → InitialCheck.runOffset EntryBinding.plan start 157 base entry j = Geometry.shimPC start (j-158) := by
    intro j lo hi; exact Geometry.whole_epilogue start (InitialCheck.rawPC EntryBinding.plan) 157 j base (entryGPR entry 30) lo hi
  have straight : ∀ j, 165 ≤ j → j ≤ 167 → InitialCheck.runOffset EntryBinding.plan start 157 base entry (j+1) = InitialCheck.runOffset EntryBinding.plan start 157 base entry j + 4#64 := by
    intro j lo hi
    rw [offPost' (j+1) (by omega) (by omega),offPost' j lo (by omega),show j+1-158=(j-158)+1 by omega]
    exact Geometry.shimPC_succ start _
  have slotPerm := Deployment.slot_permitted EntryBinding.plan raw mapping base entry start imm pins info.metadata.slotAligned
  have status31 := DefaultMTE2.rows_after_delta entry (stateAt real entry 165) (DefaultState.capacity entry+2) 1 used info.status delta (by omega)
  have low3 : (stateAt real entry 3).regs.gpr[30].toNat < 2^55 := by
    rw [pre.x30_3]; exact info.metadata.returnLow
  have target3 : (stateAt real entry 3).regs.gpr[30] = base + InitialCheck.runOffset EntryBinding.plan start 157 base entry 169 := by
    rw [pre.x30_3]
    exact Geometry.caller_target start (InitialCheck.rawPC EntryBinding.plan) 157 base (entryGPR entry 30)
  obtain ⟨epiRuns,finalInv,lr,x9,sp,mem,dit,keep,epiControl,⟨epiUsed,epiDelta,epiBound⟩,epiInvs,epiControls,epiWindow,dit34,lr34⟩ :=
    Factory.epilogue real 157 _ config rows mapping pins _ start imm _ _ base info.code.separated
      (InitialCheck.runOffset EntryBinding.plan start 157 base entry) 169 catalogue entry (stateAt real entry 3)
      (by decide) info.metadata.page aligned straight info.metadata.nodup slotPerm info.slots info.metadata.slotAligned returned
      info.metadata.mrs info.metadata.isb ctl31 info.code offPre' offPost' status31 sp31 slot31 low3 target3
  have pinsChecked : DataFrame.checkPins EntryBinding.plan = true := by decide
  have agree := DataTransport.of_pre real 157 _ config rows mapping pins _ start _ _ base base _ 169 _ (DefaultState.capacity entry+2) entry pre EntryBinding.plan pinsChecked
  obtain ⟨rt7,receipt⟩ := DitBodyEntry.of_pre real raw config rows mapping base start imm pins entry catalogue gt rt info pre
  obtain ⟨_,bodyRuns,_,fin,last,finEq,ssa,frame,pc,bodyUsed,bodyDelta,bodyBound⟩ := DitBodyRun.run real raw config rows mapping base (stateAt real entry 7) rt7 receipt
  have shift := StateShift.stateAt_add real entry 7 158
  have bodyFrame : CurrentMTE2.BodyFrame (fun pa => pa ∈ outputBytes EntryBinding.plan mapping entry) (stateAt real entry 7) (stateAt real entry 165) := by
    rw [← DataTransport.outputBytes agree]
    rw [finEq,← shift] at frame
    exact frame
  have preFields := PreABI.preserves real 157 _ config rows mapping pins _ start imm _ _ base _ 169 _ (DefaultState.capacity entry+2) entry pre
    (by decide) info.metadata.page aligned offPre' offPost' info.code slotPerm info.slots info.metadata.slotAligned info.codeSlot info.metadata.nodup
    info.metadata.rowRoom info.metadata.mrs info.metadata.isb info.metadata.land info.metadata.bodyLow 7 (by decide)
  have epiFields := EpiABI.preserves real 157 _ config rows mapping pins _ start imm _ _ base _ 169 _ entry (stateAt real entry 3)
    epiInvs epiRuns ctl31 epiControls (by decide) info.metadata.page aligned offPre' offPost' info.code slotPerm info.slots
    info.metadata.slotAligned info.metadata.nodup info.metadata.mrs info.metadata.isb status31 sp31 slot31 low3 lr34
  have bodyFields := DitBodyFrames.preserves real raw config rows mapping base (stateAt real entry 7) rt7 receipt 158 (by decide)
  rw [← shift] at bodyFields
  refine ⟨?_,?_,lr.trans pre.x30_3,?_,dit.trans savedDIT,?_,?_,?_,?_⟩
  · intro k hk
    by_cases before : k < 7
    · exact pre.runs k (by omega)
    · by_cases body : k < 165
      · have h := bodyRuns (k-7) (by omega)
        have a := StateShift.stateAt_add real entry 7 (k-7)
        have b := StateShift.stateAt_add real entry 7 (k-7+1)
        rw [← a,← b] at h
        simpa only [show 7+(k-7)=k by omega,show 7+(k-7+1)=k+1 by omega] using h
      · exact epiRuns k (by omega) (by omega)
  · exact finalInv.v1.pc.trans (Geometry.caller_target start (InitialCheck.rawPC EntryBinding.plan) 157 base (entryGPR entry 30)).symm
  · rw [sp,sp31]; exact info.metadata.sp.symm
  · intro j lo hi
    by_cases early : j ≤ 7
    · exact pre.ditOn j lo early
    · by_cases body : j ≤ 165
      · have h := (DitBodyFrames.preserves real raw config rows mapping base (stateAt real entry 7) rt7 receipt (j-7) (by omega)).2.1
        rw [← StateShift.stateAt_add real entry 7 (j-7)] at h
        simpa only [show 7+(j-7)=j by omega] using h.trans (pre.ditOn 7 (by decide) (by decide))
      · exact (epiWindow j (by omega) hi).trans dit31
  · intro pa outside slotOutside
    exact (mem pa).trans ((bodyFrame.writes pa outside).trans (pre.memPre pa slotOutside))
  · exact ⟨used + epiUsed,choice_delta_trans delta epiDelta,by omega⟩
  · refine ⟨⟨epiFields.fpcr.trans (bodyFields.1.1.trans preFields.fpcr),epiFields.fpsr.trans (bodyFields.1.2.trans preFields.fpsr),
      epiFields.z.trans (bodyFrame.z.trans preFields.z),epiFields.tls.trans (bodyFrame.tls.trans preFields.tls)⟩,?_,mem,pre.keepPre,preFields.tls⟩
    have memberTable : ∀ i : Fin 31, 18 ≤ i.val → (RegBind.Reg.x i) ∈ DitBodyABI.preservedRegisters := by decide
    rw [finEq,← shift] at ssa
    intro i lower
    by_cases lastReg : i.val = 30
    · have equal : i = (30 : Fin 31) := Fin.ext lastReg
      subst i
      exact lr.trans pre.x30_3
    · have rawKept := DitBodyABI.preserved_of_agrees mapping (stateAt real entry 7) (stateAt real entry 165) ssa (.x i) (memberTable i lower)
      exact (keep i (by omega) lastReg).trans (rawKept.trans (pre.keepPre i (by omega) lastReg))

end Entry
#print axioms of_initial
theorem run (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (start : Nat) (imm : BitVec 26) (pins : HeapV2E17.Pins) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)

    (checked : InitialCheck.check EntryBinding.plan raw config rows mapping base (referenceImageI SecpArtifact.elf base (fun _ => 0))
      start imm 157 pins (DefaultState.capacity entry+2) entry catalogue = true) :
    (∀ k, k < 169 → modelStep real (stateAt real entry k) = .ok () (stateAt real entry (k+1))) ∧
    (stateAt real entry 169).regs._PC = entryGPR entry 30 ∧
    (stateAt real entry 169).regs.gpr[30] = entry.regs.gpr[30] ∧
    (stateAt real entry 169).regs.SP_EL0 = entry.regs.SP_EL0 ∧
    (stateAt real entry 169).regs.PSTATE.DIT = entry.regs.PSTATE.DIT ∧
    (∀ j, 5 ≤ j → j ≤ 167 → (stateAt real entry j).regs.PSTATE.DIT = 1#1) ∧
    (∀ pa, pa ∉ outputBytes EntryBinding.plan mapping entry → ¬ RtShim2.ShimMem.slotBytes pins mapping pa →
      (stateAt real entry 169).mem[pa]? = entry.mem[pa]?) ∧
    (∃ used, ChoiceDelta entry (stateAt real entry 169) used ∧ used ≤ DefaultState.capacity entry+2) ∧
    ShimABI.Fields entry (stateAt real entry 169) ∧
    (∀ i : Fin 31, 18 ≤ i.val → (stateAt real entry 169).regs.gpr[i.val] = entry.regs.gpr[i.val]) ∧
    (∀ pa : Nat, (stateAt real entry 169).mem[pa]? = (stateAt real entry 165).mem[pa]?) ∧
    (∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → (stateAt real entry 7).regs.gpr[i.val] = entry.regs.gpr[i.val]) ∧
    ArmCertMemPipe.TLSFrame.tp (stateAt real entry 7) = ArmCertMemPipe.TLSFrame.tp entry := by
  obtain ⟨gt,rt,conditions⟩ := InitialCheck.of_check EntryBinding.plan raw config rows mapping base _ start imm 157 pins (DefaultState.capacity entry+2) entry catalogue checked
  have info := Initial.of_conditions EntryBinding.plan raw config rows mapping base _ start imm 157 pins (DefaultState.capacity entry+2) entry catalogue gt rt conditions
  exact of_initial real raw config rows mapping base start imm pins entry catalogue gt rt info

#print axioms run
end PipeLean_D234_SecpMul_c16.Shim32Run
