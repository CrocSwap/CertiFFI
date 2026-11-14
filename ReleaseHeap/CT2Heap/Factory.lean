-- GENERATED-ONCE by (Heap CT2 factory case) from base-v3 src-ren DefaultHeapShimTrace.lean (sha in SOURCES.sha256):
-- run_ct_r0 = trace with prologue -> prologueX9 and epilogue_events -> epilogue (same binders); per-run register facts at 369.
import CT2Heap.Core
import CT2Heap.Prologue
import DefaultHeapShimTrace
import RtDit6.ShimPre
import DefaultHeapShimClass
import DefaultHeapShimPrologueEvents
import DefaultHeapShimEpilogueEvents
import DefaultHeapShimFactory
import DefaultHeapShimEpilogueFactory
import DefaultHeapShimBody
import DefaultHeapShimPre
import DefaultHeapShimProfiles
import DefaultHeapShimFetch
import DefaultHeapShimMem
import DefaultHeapShimEffects
import DefaultHeapShimControl
import RtShimG.RtDit2_Window
import RtShimG.RtDit3_ShimWindow
import RtDit4.Release
import RtShimG.ShimMemD
import HeapV2StepCerts.Residue.RAssembly
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open CertiFFI.Prog.Generic.ModelRunView
open NativeEntryCallerParts ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace CT2HeapCt
theorem vtab357_zero : ∀ i : Fin 31, i.val < 18 →
    ((HeapV2StepCerts.RegBind.Reg.x i), 0, (0 : Int)) ∈ HeapV2StepCerts.ValBind.vtab 357 := by decide +kernel
theorem frame_mem : ∀ i : Fin 31, 18 ≤ i.val → i.val ≠ 30 → i.val ≠ 19 → i ∈ HeapV2StepCerts.Residue.frameRegs := by decide
end CT2HeapCt
namespace ReleaseProfile.DefaultHeapShimFactory
open DefaultHeapShimPre
open NativeMteTagCheck
open RtDit.Release
open RtDit RtDit.Shim RtDit.Window RtDit.ShimEv HeapV2StepCerts
open ArmBridge.CruxGenGuarded.Release (shimPC shimData shimMap ShimPrologue ShimEpilogue)

theorem run_ct_r0 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)

    (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (e : NativeState)
    (room : (357 + 12) ≤ budget) (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (offPre : ∀ j, j ≤ 6 → offS j = shimPC j) (offPost : ∀ j, (357 + 8) ≤ j → j ≤ (357 + 11) → offS j = shimPC (j - (357 + 1)))

    (codeSlot : ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
    (inv0 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope image loadBase base offS budget 0 catalogue e)
    (entryRows : TagStatusRows e (e.choiceOcc.getD 1354 0) 112)
    (shimStatic : RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (himage : image = HeapV2.image base) (hload : loadBase = base)

    (mrsEntry : NativeEntryAdapters.MrsDit.Profile e)
    (isbEntry : NativeEntryAdapters.IsbSy.Profile e)
    (residue : RtBl.CallerInv.CallerResidue e)
    (slotE : RtShim.SlotPrem.ShimSlotPresent pins mapping e)
    (spE : e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
    (static : RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 pins.sp).toNat % 16 = 0)

    (E : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS e)
    (codeStore : ImageTableSeparated scope base mapping (Residue.StoreBytes pins mapping))
    (slotStore : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ Residue.StoreBytes pins mapping a)
    (low : (e.regs.gpr[30]'(by decide)).toNat < 2 ^ 55)
    (target : e.regs.gpr[30]'(by decide) = base + offS 369) :
    (∀ i : Fin 31, i.val < 18 → i.val ≠ 9 → (stateAt real e 369).regs.gpr[i.val] = 0#64) ∧
    (∀ i : Fin 31, 18 ≤ i.val → i.val ≠ 30 → (stateAt real e 369).regs.gpr[i.val] = e.regs.gpr[i.val]) ∧
    (stateAt real e 369).regs.gpr[30] = e.regs.gpr[30] ∧
    (stateAt real e 369).regs.gpr[9] = CT2Heap.ditImage e.regs.PSTATE.DIT ∧
    (stateAt real e 369).regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16 := by
  have page := E.S.page
  have nodup := E.S.nodup
  have land : offS 6 + sign_extend (NativeShimFetch.imm26 ++ 0#2) 64 = offS 7 := by
    rw [offPre 6 (by decide), E.hoff]
    decide
  have low6 : (base + offS 7).toNat < 2 ^ 55 := by
    rw [E.hoff]
    exact low_of _ (by decide) E.S.low
  have bodyLow : (base + offS 365).toNat < 2 ^ 55 := by
    rw [offPost 365 (by decide) (by decide)]
    exact low_of _ (by decide) E.S.low
  obtain ⟨pre, x9_3, _⟩ := CT2HeapX9.prologueX9 real spec config rows mapping pins scope image loadBase base offS
    budget catalogue 112 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  rw [himage, hload] at pre
  have rowRoom : DefaultHeapBudget.capacity + 2 ≤ 112 := by
    rw [DefaultHeapBudget.capacity_eq]
    decide
  have bodyRoom : 365 ≤ budget := Nat.le_trans (by decide : 365 ≤ 369) room
  obtain ⟨inv365, sp365, slot365⟩ := DefaultHeapShimBody.return_current real spec config rows mapping
    base pins scope offS budget e catalogue 112 E pre bodyRoom rowRoom bodyLow codeStore slotStore
  obtain ⟨bodyControl, _, _, rows365⟩ := DefaultHeapShimBody.body_transport real spec config rows
    mapping base pins scope offS budget e catalogue 112 E pre bodyRoom rowRoom bodyLow
  have straight : ∀ j, 365 ≤ j → j ≤ 367 → offS (j + 1) = offS j + 4#64 := by
    intro j lo hi
    rw [offPost (j + 1) (by omega) (by omega), offPost j lo (by omega),
      show j + 1 - 358 = (j - 358) + 1 by omega, shimPC_succ]
  obtain ⟨preInv, preEv⟩ := prologue_events real spec config rows mapping pins scope image loadBase base offS
    budget catalogue 112 e room page aligned offPre offPost nodup codeSlot inv0 entryRows shimStatic
    himage hload (by decide) mrsEntry isbEntry residue slotE spE static spAligned land low6
  obtain ⟨_, _, lr369, x9_369, sp369, _, _, keep369, _, _⟩ := epilogue real spec config rows mapping pins scope (HeapV2.image base) base
    shimStatic.separated base offS budget catalogue e (stateAt real e 3) room page aligned straight
    nodup static spAligned inv365 mrsEntry isbEntry bodyControl shimStatic rfl rfl offPre offPost
    rows365 sp365 slot365 (by rw [pre.x30_3]; exact low) (pre.x30_3.trans target)
  have dp := DefaultHeapRun.body_deployment_of_prologue real 357 spec config rows mapping base pins
    scope offS budget (budget - 7) e catalogue 112 E rfl
    (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) rowRoom) pre
  have invAt := DefaultHeapRun.prefixes real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega)
  have index (j : Nat) : stateAt real e (7 + j) = stateAt real (stateAt real e 7) j :=
    RtDit.Window.stateAt_add real e 7 j
  have i357 := invAt 357 (by decide)
  have vb := i357.1.valBind.1
  have core := i357.1.body.core
  have lr := RtSaved2.lrSaved_of_chain i357.1.lr
  simp only [show (GPRSummary.key (30#5 : BitVec 5).toNat).val = 30 from by decide] at lr
  have ob := DefaultHeapCode.memFetch spec config rows mapping base (budget - 7) 357 pins
    (rowsFootprint spec.imageRows).byte catalogue dp.static 0xc0 0xd65f03c0
    (by decide) (by decide) (EntryBodyRet.W 30#5) (by decide) _ core
  obtain ⟨fin, run, _, gprRet, _, _, _, _, _, _, _⟩ :=
    DefaultHeapShimControl.shim_ret_between real spec config rows mapping _ codeScope (HeapV2.image base)
      base dp.static.separated base HeapV2Compose.offsetOf (budget - 7) 357 catalogue offS budget 365
      (by omega) (by omega) dp.page (by decide) dp.nodup _ core
      (by rw [lr, pre.x30_7]; exact bodyLow) (by rw [lr, pre.x30_7]) ob
  have bodyIndex := RtDit.Window.stateAt_add real e 7 358
  have sameFin : stateAt real e 365 = fin := by
    rw [bodyIndex]
    exact EvSteps.stateAt_succ_of run
  obtain ⟨_, frame, _, x19b, _, _⟩ := DefaultHeapRun.body_abi real spec config rows mapping base pins (stateAt real e 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp (by omega)
    (by rw [pre.x30_7]; exact bodyLow)
  simp only [show (GPRSummary.key (19#5 : BitVec 5).toNat).val = 19 from by decide] at x19b
  refine ⟨fun i h18 h9 => ?_, fun i h18 h30 => ?_, lr369.trans pre.x30_3, x9_369.trans x9_3, ?_⟩
  · rw [keep369 i h9 (by omega), sameFin, gprRet]
    exact (vb _ (CT2HeapCt.vtab357_zero i h18)).trans (by simp [HeapV2StepCerts.ValBind.vpin])
  · rw [keep369 i (by omega) h30, ← RtDit.Window.stateAt_add real e 7 358] at *
    rw [bodyIndex]
    by_cases h19 : i.val = 19
    · have e19 : i = 19 := Fin.ext h19
      subst e19
      exact x19b.trans (pre.keepPre 19 (by decide) (by decide))
    · exact (frame i (CT2HeapCt.frame_mem i h18 h30 h19)).trans (pre.keepPre i (by omega) h30)
  · rw [sp369, sp365]
#print axioms run_ct_r0
end ReleaseProfile.DefaultHeapShimFactory
