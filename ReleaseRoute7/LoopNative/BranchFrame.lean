import LoopNative.BranchStep
import RtG.NextG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace LoopNative.BranchFrame
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false

def Tail (real : Type) [Sail.SailReal real] (w : BitVec 32) (K : Int) (source : NativeState)
    (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → Crypto.BranchV2.BranchPinsV2PA fetched → NativeEntryInput.Input source fetched →
    MetadataGuard fetched → HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∃ sp a fin, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      ArmBridge.CruxGenBr.ActFrameBr (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧ BrSysEq a.regs fin.regs ∧
      fin.mem = fetched.mem ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      fin.regs.gpr = fetched.regs.gpr ∧ fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap source.regs fin.regs

theorem toTail {real : Type} [Sail.SailReal real] {w : BitVec 32} {K : Int} {source : NativeState} {next : BitVec 64}
    (framed : Tail real w K source next) : HeapV2StepCerts.BranchStepV3.BranchTailAt real w K source next := by
  intro f e b p bp input guard quiet it ss
  obtain ⟨sp, a, fin, hook, run, frame, q, pins, sys, branch, memory, gic, pc, np, gpr, spr, _⟩ :=
    framed f e b p bp input guard quiet it ss
  exact ⟨sp, a, fin, hook, run, frame, q, pins, sys, branch, memory, gic, pc, np, gpr, spr⟩

theorem entry_frame (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : Tail real w K s next)
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
    ∀ fin, modelStep real s = .ok () fin → ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap s.regs fin.regs := by
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
  obtain ⟨sp, a, fin, hook, tail, frame, q, p, sys, br, mem, gic, pc, np, gpr, spr, kept⟩ :=
    tail final enc0 budget fpins bpFinal finput guard fquiet it ss
  intro result resultRun
  have success := hstep.trans tail
  rw [resultRun] at success
  cases success
  exact kept

theorem frameG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (word : BitVec 32) (metadata : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : Tail real word metadata x (next x))
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping word x) :
    ∀ fin, modelStep real x = .ok () fin → ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap x.regs fin.regs := by
  have quiet : HookQuiet ((budget - (k + 1)) + 1) x := by
    have index : budget - (k + 1) + 1 = budget - k := by omega
    rw [index]; exact inv.v2.v1.quiet
  exact entry_frame real spec config rows mapping word metadata x inv.v2.v1.pins (next x) (offset (k + 1)) tail
    inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug (budget - (k + 1)) quiet base (offset k) inv.v2.v1.pc page aligned
    nextPlaced inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch inv.raw inv.noUpd
    obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present obligations.perAcc obligations.code
#print axioms toTail
#print axioms entry_frame
#print axioms frameG
end LoopNative.BranchFrame
