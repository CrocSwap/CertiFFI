-- the 6 trap paths over a v4-like invariant ChainInv3 ∧ V (V:= Memory's ValBindT
-- for the trap path's inputs). Branch decisions are POINTWISE at (x, V x) via the rich pointwise branch steps
-- (rich-at-v1); straight guard steps are Core's StraightV4.rich_k (ClassR); V is carried by `vcarry` from each
-- step's Holds (upds k) ∧ VEff k. Same endpoint and E17 conclusion as trap-v1.
import RtBl.TrapPaths
import RtB2.RichAt
import Bridge.CruxGenGuarded.StraightV4.All
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.ChainInvV4
open RtBl.Trap CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace RtBl.TrapV

/-- A rich class step over plan offsets, moved to `off` (equal at k, k+1), carrying V. -/
theorem straightV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (off : Nat → BitVec 64) (k : Nat) (h0 : off k = HeapV2Compose.offsetOf k) (h1 : off (k + 1) = HeapV2Compose.offsetOf (k + 1))
    (rich : RichStep real (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins k) (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins (k + 1)) (ClassR k))
    (vc : ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  obtain ⟨fin, run, inv', r⟩ := rich x (inv_congr inv h0)
  exact ⟨fin, run, inv_congr inv' h1.symm, vc x fin inv v r.1 r.2.1⟩

/-- A guard CBZ at k under `off`, decision pointwise at (x, V x), carrying V. -/
theorem brStepV_cbz (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
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
    (dec : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x → V k x → (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ taken = true))
    (vc : ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  obtain ⟨fin, run, inv', r⟩ := RtB2.RichG.rich_branch_cbz_at real spec config rows mapping _ HeapV2StepCerts.codeScope
    (HeapV2.image base) base static.separated base off budget pins k room hk page aligned upd0 veff Rt imm19 taken
    noEret x inv (dec x inv v)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, BitVec.add_assoc]; exact lowT)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, land]; cases taken <;> simp [BitVec.add_assoc])
    (fun x inv => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget k pins table static offk
      wordNat member here _ wordEq x (inv_congr inv hereN).v2)
  exact ⟨fin, run, inv', vc x fin inv v r.1 r.2.1⟩

/-- A guard B.cond at k under `off`, decision pointwise at (x, V x), carrying V. -/
theorem brStepV_bcond (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
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
    (dec : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x → V k x → (Crypto.BcondCore.bcondC cond x.regs ↔ taken = true))
    (vc : ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f) :
    Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins (k + 1) x ∧ V (k + 1) x) := by
  intro x ⟨inv, v⟩
  obtain ⟨fin, run, inv', r⟩ := RtB2.RichG.rich_branch_bcond_at real spec config rows mapping _ HeapV2StepCerts.codeScope
    (HeapV2.image base) base static.separated base off budget pins k room hk page aligned upd0 veff cond imm19 taken
    noEret x inv (dec x inv v)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, BitVec.add_assoc]; exact lowT)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, land]; cases taken <;> simp [BitVec.add_assoc])
    (fun x inv => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget k pins table static offk
      wordNat member here _ wordEq x (inv_congr inv hereN).v2)
  exact ⟨fin, run, inv', vc x fin inv v r.1 r.2.1⟩

/-- Trap path 0 over ChainInv3 ∧ V (V: the trap path's value binding, e.g. Memory's ValBindT). -/
theorem trap0_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 1 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 1 → ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 1 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 1).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 1 → Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 := by omega
        rcases hk' with rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 1) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 true
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
  have init : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ V k x) 1 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k x ∧ V k x) 1 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 1 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 1 over ChainInv3 ∧ V (V: the trap path's value binding, e.g. Memory's ValBindT). -/
theorem trap1_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 2 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 2 → ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 2 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 2).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 2 → Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 2) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 2) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 true
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
  have init : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ V k x) 2 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k x ∧ V k x) 2 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 2 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 2 over ChainInv3 ∧ V (V: the trap path's value binding, e.g. Memory's ValBindT). -/
theorem trap2_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 4 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 4 → ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 4 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 4).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 4 → Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 4) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 4) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 4) 2
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_2 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 4) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 true
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
  have init : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k x ∧ V k x) 4 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k x ∧ V k x) 4 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 4 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 3 over ChainInv3 ∧ V (V: the trap path's value binding, e.g. Memory's ValBindT). -/
theorem trap3_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 6 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 6 → ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 5 x → V 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 6 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 6).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 6 → Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 6) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 6) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 6) 2
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_2 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 6) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 false
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 6) 4
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_4 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 4 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 6) 5 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 174#19 true
            (by decide) 20 1409291713 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
            (vcarry 5 (by omega))
  have init : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k x ∧ V k x) 6 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k x ∧ V k x) 6 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 6 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 4 over ChainInv3 ∧ V (V: the trap path's value binding, e.g. Memory's ValBindT). -/
theorem trap4_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 8 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 8 → ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 5 x → V 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_7 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 7 x → V 7 x →
      (Crypto.BcondCore.bcondC 3#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 8 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 8).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 8 → Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 8) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 8) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 8) 2
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_2 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 8) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 false
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 8) 4
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_4 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 4 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 8) 5 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 174#19 false
            (by decide) 20 1409291713 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
            (vcarry 5 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 8) 6
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_6 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 6 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 8) 7 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 3#4 172#19 true
            (by decide) 28 1409291651 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_7
            (vcarry 7 (by omega))
  have init : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k x ∧ V k x) 8 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k x ∧ V k x) 8 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 8 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 5 over ChainInv3 ∧ V (V: the trap path's value binding, e.g. Memory's ValBindT). -/
theorem trap5_runV (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte) (V : Nat → NativeState → Prop)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 10 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (vcarry : ∀ k, k < 10 → ∀ s f, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k s → V k s →
      HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) s f → HeapV2StepCerts.ValBind.VEff k s f → V (k + 1) f)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 0 x → V 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 1 x → V 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 3 x → V 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 5 x → V 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_7 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 7 x → V 7 x →
      (Crypto.BcondCore.bcondC 3#4 x.regs ↔ false = true))
    (dec_9 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 9 x → V 9 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) (initialV : V 0 entry) :
    (∀ k, k ≤ 10 → (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
        V k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 10).regs._PC = base + trapOffset := by
  have steps : ∀ k, k < 10 → Uget.Chain.Step real (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k x ∧ V k x)
      (fun x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins (k + 1) x ∧ V (k + 1) x) := by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 10) 0 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 0#5 179#19 false
            (by decide) 0 3019904608 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
            (vcarry 0 (by omega))
        · exact brStepV_cbz real spec config rows mapping base budget pins table static V (trapOff 10) 1 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#5 178#19 false
            (by decide) 4 3019904577 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
            (vcarry 1 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 10) 2
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_2 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 2 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 10) 3 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 176#19 false
            (by decide) 12 1409291777 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
            (vcarry 3 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 10) 4
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_4 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 4 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 10) 5 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 174#19 false
            (by decide) 20 1409291713 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
            (vcarry 5 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 10) 6
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_6 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 6 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 10) 7 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 3#4 172#19 false
            (by decide) 28 1409291651 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_7
            (vcarry 7 (by omega))
        · exact straightV real spec config rows mapping base budget pins table static V (trapOff 10) 8
            (by simp [trapOff]) (by simp [trapOff])
            (StraightV4.rich_8 real spec config rows mapping base budget pins table static (by omega) page)
            (vcarry 8 (by omega))
        · exact brStepV_bcond real spec config rows mapping base budget pins table static V (trapOff 10) 9 (by omega)
            (by decide) page (by simp [trapOff]) (by decide +kernel) (by decide) (by decide) 1#4 170#19 true
            (by decide) 36 1409291585 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 9 + sign_extend (170#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_9
            (vcarry 9 (by omega))
  have init : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 0 entry ∧ V 0 entry := ⟨inv_congr initial (by simp [trapOff]), initialV⟩
  have inv := invariant_prefixes real (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k x ∧ V k x) 10 steps entry init
  have e17 := E17Run.e17_along_steps real spec config rows mapping _ agrees
    (fun k x => ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k x ∧ V k x) 10 entry steps init
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.1.v2.v1.pins, h.1.v2.v1.features, h.1.v2.v1.debug,
      h.1.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.1.v2.closed)
  refine ⟨fun k hk => ⟨inv k hk, e17 k hk⟩, ?_⟩
  have pc := (inv 10 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

#print axioms straightV
#print axioms brStepV_cbz
#print axioms brStepV_bcond
#print axioms trap0_runV
#print axioms trap1_runV
#print axioms trap2_runV
#print axioms trap3_runV
#print axioms trap4_runV
#print axioms trap5_runV
end RtBl.TrapV
