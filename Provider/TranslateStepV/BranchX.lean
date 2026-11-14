-- rich-v2: branch and BL RichSteps with SCR_EL3 in R. Based on the ChainInv v3 BL step (k = 15, 150, 252: calls into the
-- copy helpers; the plan is unrolled through calls, so the callee entry is base + offset (k+1)).
-- BlTailAt = CallerBl.native_tail_x's facts over the fetched state; entry_class_next_v3_bl = Core's
-- entry_class_next_v3 with that tail (BL frame: SysEq2/BrSysEq fetched → fin, X30 dropped);
-- plan_step3_bl with upds k = [(.x 30, .drop)]; instances blStep_15/150/252.
import Bridge.CruxGenGuarded.ChainInvV3
import TranslateStepV.ClassNextX
import RtBranch.BranchStepV3
import RtB2.BlTailG
import RtBranch.BranchStepV3Classes
import HeapV2StepCerts.ValBind
import HeapV2StepCerts.MemStepsV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace TranslateStepV.BranchX
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

/-!: the branch-step VHolds producer for stepV_k, from RtB2.RichG.entry_class_next_v3_brG with a tail that also
keeps NZCV. Concludes the actual modelStep with GPRs, SP, NZCV and memory unchanged (plan entries ⟨[], none, []⟩). -/

/-- A branch tail over the fetched state that also keeps NZCV (BranchTailAt, reduced to what VHolds needs,
    plus N/Z/C/V). -/
def BranchTailNZ (real : Type) [Sail.SailReal real] (w : BitVec 32) (K : Int) (source : NativeState)
    (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → Crypto.BranchV2.BranchPinsV2PA fetched → NativeEntryInput.Input source fetched →
    MetadataGuard fetched → HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∃ sp fin, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      fin.regs.gpr = fetched.regs.gpr ∧ fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = fetched.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = fetched.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = fetched.regs.PSTATE.C ∧ fin.regs.PSTATE.V = fetched.regs.PSTATE.V ∧
      fin.mem = fetched.mem

set_option maxHeartbeats 200000 in
theorem entry_branch_next_X (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : BranchTailNZ real w K s next)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : next = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (placedImg : MemReloc.ImageOn scope image s loadBase mapping)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc →
      domain (queryOf acc) ∧ ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data
          (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (word' : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (word'.extractLsb' (8 * i) 8)) →
      word' = w) :
    ∃ fin, modelStep real s = .ok () fin ∧ fin.regs.gpr = s.regs.gpr ∧ fin.regs.SP_EL0 = s.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = s.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = s.regs.PSTATE.C ∧ fin.regs.PSTATE.V = s.regs.PSTATE.V ∧ fin.mem = s.mem := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
  have placedFinal := HeapV2StepCerts.placed_fetch placedImg separated clean fmem
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := EntryClassNext.fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  have bpFinal := EntryFetchedBranch.fetched_branch_pins acc (translateCurrent out) s final stepPins hregs bp
  obtain ⟨sp, fin, hook, tail, gprF, spF, nF, zF, cF, vF, mem⟩ :=
    tail final enc0 budget fpins bpFinal finput guard fquiet it ss
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finMem : fin.mem = s.mem := mem.trans (fmem.trans memNoUpd)
  rw [hregs] at gprF spF nF zF cF vF
  exact ⟨fin, hstep.trans tail,
    gprF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    spF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    nF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.N) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    zF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    cF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.C) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    vF.trans (ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.V) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    finMem⟩

#print axioms entry_branch_next_X

/-- VHolds of an empty plan entry from GPRs, SP and NZCV unchanged. -/
theorem vholds_nil {x y : NativeState} (g : y.regs.gpr = x.regs.gpr) (sp : y.regs.SP_EL0 = x.regs.SP_EL0)
    (n : y.regs.PSTATE.N = x.regs.PSTATE.N) (z : y.regs.PSTATE.Z = x.regs.PSTATE.Z)
    (c : y.regs.PSTATE.C = x.regs.PSTATE.C) (v : y.regs.PSTATE.V = x.regs.PSTATE.V) :
    ArmCertValue.VHolds [] none x y := by
  refine ⟨fun r => ?_, fun i => ?_⟩
  · cases r <;> simp [HeapV2StepCerts.RegBind.regVal, g, sp]
  · match i with
    | 0 => simp only [ArmCertValue.flagWord, n]
    | 1 => simp only [ArmCertValue.flagWord, z]
    | 2 => simp only [ArmCertValue.flagWord, c]
    | 3 => simp only [ArmCertValue.flagWord, v]

/-- A branch step (plan entry ⟨[], none, []⟩) from ChainInv3 at k: the actual modelStep with VHolds [] none and memory kept. -/
theorem branch_vholds (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (tail : BranchTailNZ real w K x (next x))
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem := by
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, g, sp, n, z, c, v, mem⟩ :=
    entry_branch_next_X real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, vholds_nil g sp n z c v, mem⟩

#print axioms branch_vholds
end TranslateStepV.BranchX
