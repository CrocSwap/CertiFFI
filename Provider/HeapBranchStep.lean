-- Checked heap branch continuations with symbolic register and event effects.
import HeapEntryMem
import BranchEvent
import BcondEventTail
import RetEventTail
import HeapCbzTail
import HeapBl

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.HeapBranchStep
open HeapEntryMem

structure BranchEffects {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (k : Nat) (x fin : NativeState) : Prop where
  holds : RegBind.Holds (RegBind.upds k) x fin
  value : ValBind.VEff k x fin
  mem : fin.mem = x.mem
  gpr : fin.regs.gpr = x.regs.gpr
  gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3
  z : fin.regs._Z = x.regs._Z
  events : StepEvents.EvShape spec mapping [] x fin

#check "CURRENT_DECL heap_branch"
theorem branch (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (upd0 : RegBind.upds k = []) (veff : ValBind.effAt k = .none)
    (x : NativeState) (inv : HeapInv spec config rows mapping m scope image loadBase base offset budget p k x)
    (tail : BranchEvent.BranchTailEvent real w K x (base + offset (k + 1)))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      HeapInv spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
      BranchEffects spec mapping k x fin := by
  have core := inv.core
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      gpr, sp, mem, sys, br, tco, _, _, _, _, z, events, gcs⟩ :=
    BranchEvent.entry_branch_event real spec config rows mapping w K x core.v1.pins
      (base + offset (k + 1)) (offset (k + 1)) tail core.v1.gic core.v1.features core.v1.debug
      (budget - (k + 1)) hq base (offset k) core.v1.pc page aligned rfl core.v1.current
      m core.closed scope image loadBase core.placed separated core.branch core.raw core.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  have holds := BranchStepV3.keep_holds upd0 gpr sp
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed,
    TranslateSpan.BranchMTE2.pins_step x fin core.branch sys pins br, ?_, ?_, postFrame sys core.post,
    MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr core.mode,
    MemConfigFrame.debug sys.mdscr sys.hde core.debug, ?_,
    MemConfigFrame.dcache sys.sctlr core.dcache, ?_, tco.trans core.tco⟩,
    RegBind.carry_step hk holds inv.regBind, ?_⟩,
    ⟨holds, ValBind.veff_none veff x fin, mem, gpr, gcs, z, events⟩⟩
  · rw [mem]; exact core.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact core.noUpd wr acc hs
  · rw [sys.feat]; exact core.feat
  · rw [sys.feat]; exact core.mte2
  · intro e he n hn i hi; rw [mem]; exact inv.present e he n hn i hi

structure LinkEffects {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (k : Nat) (x fin : NativeState) : Prop where
  holds : RegBind.Holds (RegBind.upds k) x fin
  value : ValBind.VEff k x fin
  mem : fin.mem = x.mem
  link : fin.regs.gpr[30] = x.regs._PC + 4#64
  gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3
  z : fin.regs._Z = x.regs._Z
  events : StepEvents.EvShape spec mapping [] x fin

#check "CURRENT_DECL heap_bl"
theorem bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (imm26 : BitVec 26)
    (upd : RegBind.upds k = [(.x 30, .drop)]) (veff : ValBind.effAt k = .none)
    (x : NativeState) (inv : HeapInv spec config rows mapping m scope image loadBase base offset budget p k x)
    (low : (NativeEntryCallerParts.blTarget imm26 x).toNat < 2 ^ 55)
    (controls : NativeEntryCallerParts.CallerControls x)
    (nextPlaced : NativeEntryCallerParts.blTarget imm26 x = base + offset (k + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      HeapInv spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
      LinkEffects spec mapping k x fin := by
  have core := inv.core
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp,
      gpr, sp, mem, sys, tco, z, gcs, events⟩ :=
    HeapBl.entry_bl real spec config rows mapping imm26 x core.v1.pins (offset (k + 1)) low controls
      core.v1.gic core.v1.features core.v1.debug (budget - (k + 1)) hq base (offset k) core.v1.pc
      page aligned nextPlaced core.v1.current m core.closed scope image loadBase core.placed separated
      core.branch core.raw core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc nodup ob.code
  have holds := BlStepV3.bl_holds upd ⟨_, gpr⟩ sp
  have link : fin.regs.gpr[30] = x.regs._PC + 4#64 := by rw [gpr, Vector.getElem_set_self]
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp, ?_, ?_,
    postFrame sys core.post, MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr core.mode,
    MemConfigFrame.debug sys.mdscr sys.hde core.debug, ?_,
    MemConfigFrame.dcache sys.sctlr core.dcache, ?_, tco.trans core.tco⟩,
    RegBind.carry_step hk holds inv.regBind, ?_⟩, ⟨holds, ValBind.veff_none veff x fin, mem, link, gcs, z, events⟩⟩
  · rw [mem]; exact core.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact core.noUpd wr acc hs
  · rw [sys.feat]; exact core.feat
  · rw [sys.feat]; exact core.mte2
  · intro e he n hn i hi; rw [mem]; exact inv.present e he n hn i hi

#print axioms branch
#print axioms bl
end ReleaseProfile.HeapBranchStep
