-- Actual normal heap body, terminal RET, and ordered event trace.
import DefaultHeapRun
import RtPremC.PremC
import DefaultRetEventTail
import Bridge.CruxGenGuarded.EvSteps.CT

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapRun

#check "CURRENT_DECL heap body_ret"
theorem body_ret_full (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    let x := stateAt real entry 357
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._PC = entry.regs.gpr[30] ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧ fin.mem = x.mem ∧
      fin.regs._Z = x.regs._Z ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3 ∧
      StepEvents.EvShape spec mapping [] x fin ∧
      RtPremC.CtlRel spec entry fin ∧
      (∃ used, NativeMteTagCheck.ChoiceDelta entry fin used ∧ used ≤ drawsBefore 357) := by
  intro x
  have inv : RunInv spec config rows mapping base pins entry budget 357 catalogue capacity drawsBefore x :=
    prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp (by omega) 357 (by decide)
  have core := inv.1.body.core
  have lr := RtSaved2.lrSaved_of_chain inv.1.lr
  let w := EntryBodyRet.W 30#5
  have ob := DefaultHeapCode.memFetch spec config rows mapping base budget 357 pins (rowsFootprint spec.imageRows).byte catalogue
    dp.static 0xc0 0xd65f03c0 (by decide) (by decide) w (by decide) x core
  let target := entry.regs.gpr[30]
  have tail := DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide)
    (by rw [lr]; exact low) target lr
  have placed : target = base + (target - base) := by rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hq : HookQuiet ((budget - 358) + 1) x := by
    have e : budget - 358 + 1 = budget - 357 := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, _, _, _, pc, _, _, _, _, _, gpr, sp, mem, _, _, _, _, _, _, _, z, ev, gcs, control, choice⟩ :=
    DefaultBranchEvent.entry_branch_event real spec config rows mapping w 94 x core.v1.pins target
      (target - base) tail core.v1.gic core.v1.features core.v1.debug (budget - 358) hq base
      (HeapV2Compose.offsetOf 357) core.v1.pc dp.page (by decide) placed core.v1.current
      _ core.closed codeScope (HeapV2.image base) base core.placed dp.static.separated
      core.branch core.raw core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code dp.nodup
  obtain ⟨used, prefixChoice, prefixBound⟩ := inv.1.body.trace
  exact ⟨fin, run, pc.trans placed.symm, gpr, sp, mem, z, gcs, ev,
    inv.1.body.control.trans control,
    used, by simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans prefixChoice choice,
    prefixBound⟩

theorem body_ret (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    let x := stateAt real entry 357
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._PC = entry.regs.gpr[30] ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧ fin.mem = x.mem ∧
      fin.regs._Z = x.regs._Z ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  obtain ⟨fin, run, pc, gpr, sp, mem, z, gcs, events, _, _⟩ :=
    body_ret_full real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb low
  exact ⟨fin, run, pc, gpr, sp, mem, z, gcs, events⟩

#print axioms body_ret_full
#check "CURRENT_DECL heap body_abi"
theorem body_abi (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    let fin := stateAt real entry 358
    fin.regs._PC = entry.regs.gpr[30] ∧
    (∀ r ∈ Residue.frameRegs, RegBind.regVal fin (.x r) = RegBind.regVal entry (.x r)) ∧
    fin.regs.gpr[(GPRSummary.key (30#5 : BitVec 5).toNat).val] = entry.regs.gpr[30] ∧
    fin.regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = entry.regs.gpr[19] ∧
    fin.regs.SP_EL0 = entry.regs.SP_EL0 ∧
    (∀ a, ¬ Residue.StoreBytes pins mapping a → fin.mem[a]? = entry.mem[a]?) := by
  dsimp only
  have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp (by omega) 357 (by decide)
  obtain ⟨out, run, pc, gpr, sp, mem, _, _, _⟩ := body_ret real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb low
  have sp0 := dp.init.regBind (.sp, 0, 0) (by decide)
  have sp357 := inv.1.body.regBind (.sp, 0, 0) (by decide)
  simp only [RegBind.regVal] at sp0 sp357
  rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
  exact ⟨pc, fun r hr => by simpa only [RegBind.regVal, gpr] using inv.2.1.1 r hr,
    gpr ▸ RtSaved2.lrSaved_of_chain inv.1.lr, gpr ▸ RtSaved3.x19_of_chain inv.2.2,
    sp.trans (sp357.trans sp0.symm), fun a ha => by rw [mem]; exact inv.2.1.2 a ha⟩

#print axioms body_ret
#print axioms body_abi

#check "CURRENT_DECL heap body_ct"
theorem body_ct (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry1 entry2 : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp1 : DeploymentPremises spec config rows mapping base pins entry1 budget catalogue capacity drawsBefore)
    (dp2 : DeploymentPremises spec config rows mapping base pins entry2 budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry1.regs.gpr[30].toNat < 2 ^ 55) (lr : entry1.regs.gpr[30] = entry2.regs.gpr[30]) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record entry1 entry2
      (stateAt real entry1 358) (stateAt real entry2 358) := by
  have i1 := prefixes real spec config rows mapping base pins entry1 budget catalogue capacity drawsBefore dp1 (by omega)
  have i2 := prefixes real spec config rows mapping base pins entry2 budget catalogue capacity drawsBefore dp2 (by omega)
  refine PhasedCT.phased_records (stateAt real entry1) (stateAt real entry2) (fun _ _ _ => True)
    358 trivial (by rw [(i1 0 (by omega)).1.body.core.v1.pc, (i2 0 (by omega)).1.body.core.v1.pc]) ?_
  intro k hk _
  have pc : (stateAt real entry1 k).regs._PC = (stateAt real entry2 k).regs._PC := by
    rw [(i1 k (by omega)).1.body.core.v1.pc, (i2 k (by omega)).1.body.core.v1.pc]
  refine ⟨?_, trivial⟩
  by_cases earlier : k < 357
  · obtain ⟨f1, r1, n1, _, e1⟩ :=
      steps real spec config rows mapping base pins entry1 budget catalogue capacity drawsBefore dp1 (by omega) k earlier _ (i1 k (by omega))
    obtain ⟨f2, r2, n2, _, e2⟩ :=
      steps real spec config rows mapping base pins entry2 budget catalogue capacity drawsBefore dp2 (by omega) k earlier _ (i2 k (by omega))
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of r1, ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of r2]
    exact StepEvents.pair spec mapping (records spec pins k) _ _ _ _ e1 e2 pc
      (by rw [n1.1.body.core.v1.pc, n2.1.body.core.v1.pc])
  · have last : k = 357 := by omega
    subst k
    obtain ⟨f1, r1, p1, _, _, _, _, _, e1⟩ := body_ret real spec config rows mapping base pins entry1 budget catalogue capacity drawsBefore dp1 hb low
    obtain ⟨f2, r2, p2, _, _, _, _, _, e2⟩ :=
      body_ret real spec config rows mapping base pins entry2 budget catalogue capacity drawsBefore dp2 hb (by rw [← lr]; exact low)
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of r1, ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of r2]
    exact StepEvents.pair spec mapping [] _ _ _ _ e1 e2 pc (p1.trans (lr.trans p2.symm))

#print axioms body_ct

#check "CURRENT_DECL default heap body_return_transport"
theorem body_return_transport (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    RtPremC.CtlRel spec entry (stateAt real entry 358) ∧
    (∃ used, NativeMteTagCheck.ChoiceDelta entry (stateAt real entry 358) used ∧ used ≤ drawsBefore 357) := by
  obtain ⟨fin, run, _, _, _, _, _, _, _, control, trace⟩ := body_ret_full real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb low
  rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
  exact ⟨control, trace⟩

#print axioms body_return_transport

#check "CURRENT_DECL default heap body_return_closed"
theorem body_return_closed (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping consumer (beforeFetchState entry)) :
    ClosedMembershipAt spec config rows mapping consumer (beforeFetchState (stateAt real entry 358)) :=
  RtPremC.closed_across closed (body_return_transport real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb low).1

#print axioms body_return_closed
end ReleaseProfile.DefaultHeapRun
