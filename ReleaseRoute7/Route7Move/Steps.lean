-- Route 7 breadth: CurrentInv steps for memmove's CMP (SUBS XZR, shifted reg), ADD (shifted reg) and
-- B.cond, as Route7Steps wrappers (classEventStep / branchEventStep + the route frame lemmas), and the CMP→B.cond link.
import Route7Steps.Class
import Route7Steps.Branch
import Route7Move.BcondTailFrame
import ArmCertValueTail14.SubsShift64ZRd
import ArmCertValueTail14.AddShift64
import PipeR14Next.Common
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false

namespace Route7Move

/-- CMP Xn, Xm (SUBS XZR, Xn, Xm) over CurrentInv: no register written, NZCV := sbc3 flags of (Xn, Xm, 1). -/
theorem subsShift64ZRd (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rn Rm : BitVec 5) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] (some (ArmCertValue.R14.SubsShift64ZRd.fl Rn Rm)) x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame NativeEntryBodyFlag.SubsShift64ZRd.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm)
    NativeEntryBodyFlag.SubsShift64ZRd.writes 17 [] (some (ArmCertValue.R14.SubsShift64ZRd.fl Rn Rm))
    (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.SubsShift64ZRd.tailX real x Rn 0#6 Rm rn rm rfl noEret)
    (ReleaseProfile.DefaultRuntimeScalarChoice.tail_SubsShift64ZRd real x Rn 0#6 Rm rn rm noEret) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, _, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm)
      NativeEntryBodyFlag.SubsShift64ZRd.writes 17 [] (some (ArmCertValue.R14.SubsShift64ZRd.fl Rn Rm))
      (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.SubsShift64ZRd.tailX real x Rn 0#6 Rm rn rm rfl noEret)
      (ReleaseProfile.DefaultRuntimeScalarChoice.tail_SubsShift64ZRd real x Rn 0#6 Rm rn rm noEret) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice⟩

/-- ADD Xd, Xn, Xm (shifted reg, LSL #0) over CurrentInv. -/
theorem addShift64 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame NativeEntryBodyAdapters.AddShift64.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm)
    NativeEntryBodyAdapters.AddShift64.writes 14 (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none
    (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.AddShift64.tailX real x Rd Rn 0#6 Rm rd rn rm rfl noEret ⟨⟩)
    (ReleaseProfile.DefaultRuntimeScalarChoice.tail_AddShift64 real x Rd Rn 0#6 Rm rd rn rm ⟨⟩ noEret) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, _, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm)
      NativeEntryBodyAdapters.AddShift64.writes 14 (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none
      (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.AddShift64.tailX real x Rd Rn 0#6 Rm rd rn rm rfl noEret ⟨⟩)
      (ReleaseProfile.DefaultRuntimeScalarChoice.tail_AddShift64 real x Rd Rn 0#6 Rm rd rn rm ⟨⟩ noEret) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice⟩

attribute [local instance 10] Classical.propDecidable in
/-- B.cond over CurrentInv: successor PC = nextPC (taken target or PC+4 by bcondC on the current NZCV). -/
theorem bcond (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (cond : BitVec 4) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs._PC + sign_extend (imm19 +++ 0#2) 64).toNat < 2 ^ 55) (nextPC : BitVec 64)
    (hnext : (if Crypto.BcondCore.bcondC cond x.regs then x.regs._PC + sign_extend (imm19 +++ 0#2) 64
      else x.regs._PC + 4#64) = nextPC)
    (nextPlaced : nextPC = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventStep_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) 69
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x cond imm19 noEret hlow nextPC hnext)
      (ReleaseProfile.Route7BcondTailFrame.tail_at real x cond imm19 noEret hlow nextPC hnext)
      nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, _, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) 69
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x cond imm19 noEret hlow nextPC hnext)
      nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice⟩

/-! ## CMP X0, X1 → B.EQ / B.LO -/

theorem add_not_one (a b : BitVec 64) : a + ~~~b + 1#64 = a - b := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]

theorem carry_iff (a b : BitVec 64) : (2 ^ 64 ≤ a.toNat + (~~~b).toNat + (1#64).toNat) ↔ b.toNat ≤ a.toNat := by
  rw [BitVec.toNat_not]
  have hb := b.isLt
  simp only [BitVec.toNat_ofNat]
  omega

/-- After CMP X0, X1: B.EQ (cond 0) is taken iff X0 = X1. -/
theorem cmp_eq (x y : NativeState)
    (h : ArmCertValue.VHolds [] (some (ArmCertValue.R14.SubsShift64ZRd.fl 0#5 1#5)) x y) :
    Crypto.BcondCore.bcondC 0#4 y.regs ↔ x.regs.gpr[0] = x.regs.gpr[1] := by
  obtain ⟨_, _, fz, _, _⟩ := h
  change y.regs.PSTATE.Z.setWidth 64 = ArmCertValue.b01 (x.regs.gpr[0] + ~~~x.regs.gpr[1] + 1#64 == 0) at fz
  rw [PipeR14Next.cond_bridge 0#4 y.regs (x.regs.gpr[0] == x.regs.gpr[1])]
  · simp
  · simp only [ArmCertValue.condHolds, fz, add_not_one]
    by_cases he : x.regs.gpr[0] = x.regs.gpr[1]
    · have hz : x.regs.gpr[0] - x.regs.gpr[1] = 0#64 := by rw [he, BitVec.sub_self]
      simp [hz, he, ArmCertValue.b01]
    · have hz : x.regs.gpr[0] - x.regs.gpr[1] ≠ 0#64 := by intro h0; apply he; bv_omega
      simp [hz, he, ArmCertValue.b01]

/-- After CMP X0, X1: B.LO / B.CC (cond 3) is taken iff X0 <u X1. -/
theorem cmp_lo (x y : NativeState)
    (h : ArmCertValue.VHolds [] (some (ArmCertValue.R14.SubsShift64ZRd.fl 0#5 1#5)) x y) :
    Crypto.BcondCore.bcondC 3#4 y.regs ↔ x.regs.gpr[0].toNat < x.regs.gpr[1].toNat := by
  obtain ⟨_, _, _, fc, _⟩ := h
  change y.regs.PSTATE.C.setWidth 64 =
    ArmCertValue.b01 (decide (2 ^ 64 ≤ x.regs.gpr[0].toNat + (~~~x.regs.gpr[1]).toNat + (1#64).toNat)) at fc
  rw [PipeR14Next.cond_bridge 3#4 y.regs (decide (x.regs.gpr[0].toNat < x.regs.gpr[1].toNat))]
  · simp
  · simp only [ArmCertValue.condHolds, fc, carry_iff]
    by_cases hl : x.regs.gpr[0].toNat < x.regs.gpr[1].toNat
    · have : ¬ x.regs.gpr[1].toNat ≤ x.regs.gpr[0].toNat := by omega
      simp [this, hl, ArmCertValue.b01]
    · have : x.regs.gpr[1].toNat ≤ x.regs.gpr[0].toNat := by omega
      simp [this, hl, ArmCertValue.b01]

end Route7Move
#print axioms Route7Move.subsShift64ZRd
#print axioms Route7Move.addShift64
#print axioms Route7Move.bcond
#print axioms Route7Move.cmp_eq
#print axioms Route7Move.cmp_lo
