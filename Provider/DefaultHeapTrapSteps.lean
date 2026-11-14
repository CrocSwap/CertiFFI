import DefaultHeapTrapBase
import DefaultHeapResidue
import RtT.TrapV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open HeapV2StepCerts CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV4
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapTrap
attribute [local instance 10] Classical.propDecidable


theorem straightV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (off : Nat → BitVec 64) (k : Nat) (h0 : off k = HeapV2Compose.offsetOf k) (h1 : off (k + 1) = HeapV2Compose.offsetOf (k + 1))
    (rich : RichStep real (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf k) (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf (k + 1)) (DefaultHeapClassStep.Effects spec mapping k))
    (vc : ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry off k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry off k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry off (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  obtain ⟨fin, run, next, effect⟩ := rich x (inv_congr inv h0)
  exact ⟨fin, run, ⟨inv_congr next h1.symm, vc x fin inv v effect.holds effect.value⟩, effect.z, effect.events⟩

#print axioms straightV

theorem brStepV_cbz (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (off : Nat → BitVec 64) (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (hereN : off k = HeapV2Compose.offsetOf k) (aligned : (off k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (Rt : BitVec 5) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (offk wordNat : Nat) (member : (offk, wordNat) ∈ HeapV2Plan.codeWords)
    (here : HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + offk))
    (wordEq : EntryBodyCbz.W Rt imm19 = BitVec.ofNat 32 wordNat)
    (land : off (k + 1) = if taken then HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64 else HeapV2Compose.offsetOf k + 4#64)
    (lowT : (base + (HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (dec : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry off k x → V k x → (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ taken = true))
    (vc : ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry off k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry off k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry off (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  have low : (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.core.v1.pc, hereN, BitVec.add_assoc]
    exact lowT
  have target : (if Crypto.CruxCbz.cbzC 1#1 Rt x then x.regs._PC + sign_extend (imm19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + off (k + 1) := by
    have decision := dec x inv v
    rw [inv.core.v1.pc, hereN, land]
    cases taken <;> simp_all [BitVec.add_assoc]
  obtain ⟨fin, run, next, effect⟩ := DefaultHeapBranchStep.branch real spec config rows mapping _
    codeScope (HeapV2.image base) base static.separated base off budget pins k catalogue entry 0 (fun _ => 0)
    (Nat.le_refl _) room hk page aligned _ 118 upd0 veff x inv
    (DefaultHeapCbzTail.tail_at real x Rt imm19 noEret low _ target) nodup
    (fetchOn S spec config rows mapping base budget k pins table catalogue static offk wordNat member
      here _ wordEq x (inv_congr inv hereN).core)
  exact ⟨fin, run, ⟨next, vc x fin inv v effect.holds effect.value⟩, effect.z, effect.events⟩

#print axioms brStepV_cbz

theorem brStepV_bcond (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (nodup : (spec.logicalRows.map (·.logical)).Nodup) (V : Nat → NativeState → Prop)
    (off : Nat → BitVec 64) (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (hereN : off k = HeapV2Compose.offsetOf k) (aligned : (off k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (cond : BitVec 4) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (offk wordNat : Nat) (member : (offk, wordNat) ∈ HeapV2Plan.codeWords)
    (here : HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + offk))
    (wordEq : EntryBodyBcond.W cond imm19 = BitVec.ofNat 32 wordNat)
    (land : off (k + 1) = if taken then HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64 else HeapV2Compose.offsetOf k + 4#64)
    (lowT : (base + (HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (dec : ∀ x, BaseInv spec config rows mapping S base budget pins table catalogue entry off k x → V k x → (Crypto.BcondCore.bcondC cond x.regs ↔ taken = true))
    (vc : ∀ s f, BaseInv spec config rows mapping S base budget pins table catalogue entry off k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    DefaultHeapResidue.Step real spec mapping [] (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry off k x ∧ V k x)
      (fun x => BaseInv spec config rows mapping S base budget pins table catalogue entry off (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  have low : (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [inv.core.v1.pc, hereN, BitVec.add_assoc]
    exact lowT
  have target : (if Crypto.BcondCore.bcondC cond x.regs then x.regs._PC + sign_extend (imm19 ++ 0#2) 64
      else x.regs._PC + 4#64) = base + off (k + 1) := by
    have decision := dec x inv v
    rw [inv.core.v1.pc, hereN, land]
    cases taken <;> simp_all [BitVec.add_assoc]
  obtain ⟨fin, run, next, effect⟩ := DefaultHeapBranchStep.branch real spec config rows mapping _
    codeScope (HeapV2.image base) base static.separated base off budget pins k catalogue entry 0 (fun _ => 0)
    (Nat.le_refl _) room hk page aligned _ 69 upd0 veff x inv
    (DefaultBcondEventTail.tail_at real x cond imm19 noEret low _ target) nodup
    (fetchOn S spec config rows mapping base budget k pins table catalogue static offk wordNat member
      here _ wordEq x (inv_congr inv hereN).core)
  exact ⟨fin, run, ⟨next, vc x fin inv v effect.holds effect.value⟩, effect.z, effect.events⟩

#print axioms brStepV_bcond

theorem rich_2 (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (budget : Nat)
    (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 2 < budget) (page : base.toNat % 4096 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    RichStep real
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 2)
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf (2 + 1))
      (DefaultHeapClassStep.Effects spec mapping 2) := by
  intro x inv
  exact DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 2 catalogue entry 0 (fun _ => 0) (Nat.le_refl _) room (by decide) page (by decide)
      _ _ _ x inv (HeapV2StepCerts.TailWE.tailW_2 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_21
        all_goals first | decide | constructor)
      (by rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1) nodup
      (fetchOn S spec config rows mapping base budget 2 pins table catalogue static 0x8 0xf240081f
        (by decide) (by decide) _ (by decide) x inv.core)

#print axioms rich_2

theorem rich_4 (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (budget : Nat)
    (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 4 < budget) (page : base.toNat % 4096 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    RichStep real
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 4)
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf (4 + 1))
      (DefaultHeapClassStep.Effects spec mapping 4) := by
  intro x inv
  exact DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 4 catalogue entry 0 (fun _ => 0) (Nat.le_refl _) room (by decide) page (by decide)
      _ _ _ x inv (HeapV2StepCerts.TailWE.tailW_4 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_21
        all_goals first | decide | constructor)
      (by rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1) nodup
      (fetchOn S spec config rows mapping base budget 4 pins table catalogue static 0x10 0xf240083f
        (by decide) (by decide) _ (by decide) x inv.core)

#print axioms rich_4

theorem rich_6 (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (budget : Nat)
    (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 6 < budget) (page : base.toNat % 4096 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    RichStep real
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 6)
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf (6 + 1))
      (DefaultHeapClassStep.Effects spec mapping 6) := by
  intro x inv
  exact DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 6 catalogue entry 0 (fun _ => 0) (Nat.le_refl _) room (by decide) page (by decide)
      _ _ _ x inv (HeapV2StepCerts.TailWE.tailW_6 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_20
        all_goals first | decide | constructor)
      (by rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1) nodup
      (fetchOn S spec config rows mapping base budget 6 pins table catalogue static 0x18 0xf100805f
        (by decide) (by decide) _ (by decide) x inv.core)

#print axioms rich_6

theorem rich_8 (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (budget : Nat)
    (pins : HeapV2E17.Pins) (table : Nat → Prop) (S : Nat × Nat × Int × Nat × Bool → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 8 < budget) (page : base.toNat % 4096 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    RichStep real
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf 8)
      (BaseInv spec config rows mapping S base budget pins table catalogue entry HeapV2Compose.offsetOf (8 + 1))
      (DefaultHeapClassStep.Effects spec mapping 8) := by
  intro x inv
  exact DefaultHeapClassStep.step real spec config rows mapping _ codeScope (HeapV2.image base) base
      static.separated base HeapV2Compose.offsetOf budget pins 8 catalogue entry 0 (fun _ => 0) (Nat.le_refl _) room (by decide) page (by decide)
      _ _ _ x inv (HeapV2StepCerts.TailWE.tailW_8 real x)
      (by
        apply HeapScalarTagCheck.Tails.tail_20
        all_goals first | decide | constructor)
      (by rw [inv.core.v1.pc, BitVec.add_assoc]; congr 1) nodup
      (fetchOn S spec config rows mapping base budget 8 pins table catalogue static 0x20 0xf100807f
        (by decide) (by decide) _ (by decide) x inv.core)

#print axioms rich_8

end ReleaseProfile.DefaultHeapTrap
