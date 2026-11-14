import Bridge.CruxGenGuarded.ClosedChain
import Bridge.CruxGenGuarded.EntryFetchedBranch
import Bridge.CruxGenGuarded.ClassBranchPins
import HeapV2StepCerts.Carry
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.TailW
import Bridge.CruxGenGuarded.ClassNextV3
import Bridge.CruxGenGuarded.ChainInvV4
import ArmCertValueTail.Def
import HeapV2StepCerts.RawFetch
import ArmCertWalk.NativeFetchPreservingEvents
import ArmCertWalk.AccessTransfer
import Bridge.CruxGenGuarded.BookkeepingTransport
import Bridge.CruxGenGuarded.FrameTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace ArmBridge.CruxGenGuarded.ClassNextX
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/-!: the class-step VHolds producer for stepV_k. GENERATED from ClassNextV4.entry_class_next_v4 /
ChainInvV4.plan_step4_class with ClassTailXAt (value-tails-v7) as the tail: the actual modelStep, VHolds us fl x fin
(moved from the fetched state to x: the fetch keeps GPRs, SP and NZCV) and fin.mem = x.mem. -/

/-- VHolds over fetched → fin moves to s → fin when the fetch kept GPRs, SP and NZCV. -/
theorem vholds_prefix {s final fin : NativeState} {vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd)}
    {fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd)}
    (g : final.regs.gpr = s.regs.gpr) (sp : final.regs.SP_EL0 = s.regs.SP_EL0)
    (nz : final.regs.PSTATE.N = s.regs.PSTATE.N ∧ final.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
      final.regs.PSTATE.C = s.regs.PSTATE.C ∧ final.regs.PSTATE.V = s.regs.PSTATE.V)
    (h : ArmCertValue.VHolds vus fl final fin) : ArmCertValue.VHolds vus fl s fin := by
  have rv : ∀ r, HeapV2StepCerts.RegBind.regVal final r = HeapV2StepCerts.RegBind.regVal s r := by
    intro r; cases r <;> simp [HeapV2StepCerts.RegBind.regVal, g, sp]
  have fw : ∀ i, ArmCertValue.flagWord final i = ArmCertValue.flagWord s i := by
    obtain ⟨hn, hz, hc, hv⟩ := nz
    intro i; match i with
    | 0 => simp only [ArmCertValue.flagWord, hn]
    | 1 => simp only [ArmCertValue.flagWord, hz]
    | 2 => simp only [ArmCertValue.flagWord, hc]
    | 3 => simp only [ArmCertValue.flagWord, hv]
  have ev : ∀ u : ArmCertValue.VUpd, u.eval final = u.eval s := by
    intro u; unfold ArmCertValue.VUpd.eval; congr 1
    apply List.map_congr_left; intro a _
    cases a with
    | reg r => exact rv r
    | flag i => exact fw i
    | lit c => rfl
  obtain ⟨hr, hf⟩ := h
  refine ⟨fun r => ?_, ?_⟩
  · have := hr r
    revert this
    generalize (vus.find? (·.1 = r)).map (·.2) = v
    rcases v with _ | _ | u
    · intro e; rw [e, rv]
    · intro _; trivial
    · intro e; rw [e, ev]
  · cases fl with
    | none => intro i; rw [hf i, fw]
    | some q => obtain ⟨n, z, c, v⟩ := q; obtain ⟨h1, h2, h3, h4⟩ := hf; exact ⟨h1.trans (ev n), h2.trans (ev z), h3.trans (ev c), h4.trans (ev v)⟩

set_option maxHeartbeats 200000 in
theorem entry_class_next_X (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd))
    (tail : ArmCertValue.ClassTailXAt real w writes K s next vus fl)
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
    ∃ fin, modelStep real s = .ok () fin ∧ ArmCertValue.VHolds vus fl s fin ∧ fin.mem = s.mem := by
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
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, mem, gic, pc, np, ev, z, vh⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finMem : fin.mem = s.mem := mem.trans (fmem.trans memNoUpd)
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have nzFinal : final.regs.PSTATE.N = s.regs.PSTATE.N ∧ final.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
      final.regs.PSTATE.C = s.regs.PSTATE.C ∧ final.regs.PSTATE.V = s.regs.PSTATE.V := by
    rw [hregs]
    exact ⟨ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.N) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl,
      ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl,
      ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.C) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl,
      ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.V) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl⟩
  exact ⟨fin, hstep.trans tail, vholds_prefix gprFinal spFinal nzFinal vh, finMem⟩

#print axioms entry_class_next_X

end ArmBridge.CruxGenGuarded.ClassNextX

namespace ArmBridge.CruxGenGuarded.ChainInvV4X
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000

theorem class_vholds (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd))
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      ArmCertValue.ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus fl x fin ∧ fin.mem = x.mem := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact ClassNextX.entry_class_next_X real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) vus fl (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code

#print axioms class_vholds

/-- MemVHolds with no memory effects from an unchanged memory (same statement as Memory's StepVCore.memV_nil_of_mem). -/
theorem memV_nil_of_mem (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List ArmCertValue.Region)
    (x y : NativeState) (h : y.mem = x.mem) : ArmCertValue.MemVHolds mapping pinv regions [] x y := by
  refine ⟨fun e he => absurd he (List.not_mem_nil), ?_, ?_⟩
  · intro r _ w _ _ _ _
    simp only [ArmCertValue.regionWord, ArmCertValue.regionByte, h]
  · intro r _ j _ _ _ _
    simp only [ArmCertValue.regionByte, h]

#print axioms memV_nil_of_mem

/-- A single-register VHolds entry can be restated with any update of the same value at x. -/
theorem vholds_upd_congr {r : HeapV2StepCerts.RegBind.Reg} {u u' : ArmCertValue.VUpd}
    {fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd)} {x y : NativeState}
    (h : u.eval x = u'.eval x) (v : ArmCertValue.VHolds [(r, some u)] fl x y) :
    ArmCertValue.VHolds [(r, some u')] fl x y := by
  obtain ⟨hr, hf⟩ := v
  refine ⟨fun r' => ?_, hf⟩
  have := hr r'
  by_cases e : r = r'
  · subst e; simp only [List.find?_cons, decide_true, Option.map_some] at this ⊢; rw [this, h]
  · simp only [List.find?_cons, List.find?_nil, e, decide_false, Option.map_none] at this ⊢; exact this

/-- SUB SP, SP, #c as the plan writes it (sub) from the tail's add of −c. -/
theorem eval_sp_sub (x : NativeState) (c : BitVec 12) :
    (⟨.add, [.reg .sp, .lit (BitVec.ofInt 64 (-(c.toNat : Int)))]⟩ : ArmCertValue.VUpd).eval x =
      (⟨.sub, [.reg .sp, .lit (BitVec.ofNat 64 c.toNat)]⟩ : ArmCertValue.VUpd).eval x := by
  show _ + _ = _ - _
  rw [BitVec.sub_eq_add_neg]; congr 1
  show BitVec.ofInt 64 (-(c.toNat : Int)) = -(BitVec.ofNat 64 c.toNat)
  have hc := c.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_neg, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *
  omega

#print axioms vholds_upd_congr
end ArmBridge.CruxGenGuarded.ChainInvV4X
