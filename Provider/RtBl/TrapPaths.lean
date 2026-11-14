-- ((2),): the 6 heap-v2 trap paths (572d607, HEAPV2-PATHS 1..6)
-- over ChainInv v3. Trap j = the normal path's guard prefix k = 0 .. L-1 (L = 1,2,4,6,8,10), every guard
-- branch not taken except the last, which is taken to certiffi_trap (entry offset 716). The endpoint is that
-- target (the trap stub is not executed). Offsets: trapOff L i = plan offset for i ≠ L, 716 at i = L.
-- Straight guard steps reuse Memory's StraightV3.step3_k (offset congruence); branch steps are
-- plan_step3_branch_{cbz,bcond} with explicit per-step decisions `dec_k` (the trap-path input
-- condition, cf. Memory's NormalPath/dec_k) and the taken target's placement decided from the plan word.
import RtBranch.BranchStepV3Classes
import Bridge.CruxGenGuarded.StraightV3.All
import HeapV2StepCerts.MemStepV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace RtBl.Trap

/-- certiffi_trap: entry-relative offset 716. -/
def trapOffset : BitVec 64 := BitVec.ofNat 64 (0x10278 + 716)

/-- Trap path of length L: plan offsets, then the trap target at index L. -/
def trapOff (L : Nat) (i : Nat) : BitVec 64 := if i = L then trapOffset else HeapV2Compose.offsetOf i

theorem inv_congr {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop} {image : MemReloc.Image}
    {loadBase : MemReloc.Word} {base : BitVec 64} {offset offset' : Nat → BitVec 64} {budget : Nat}
    {p : HeapV2E17.Pins} {k : Nat} {x : NativeState}
    (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (h : offset k = offset' k) : ChainInv3 spec config rows mapping m scope image loadBase base offset' budget p k x :=
  ⟨⟨⟨inv.v2.v1.pins, inv.v2.v1.features, inv.v2.v1.debug, inv.v2.v1.current, inv.v2.v1.quiet, inv.v2.v1.gic,
      inv.v2.v1.pc.trans (by rw [h])⟩, inv.v2.closed, inv.v2.placed, inv.v2.branch⟩,
    inv.regBind, inv.present, inv.raw, inv.noUpd, inv.post2, inv.mode, inv.debug, inv.feat, inv.dcache⟩

theorem step_congr (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop} {image : MemReloc.Image}
    {loadBase : MemReloc.Word} {base : BitVec 64} {offset offset' : Nat → BitVec 64} {budget : Nat}
    {p : HeapV2E17.Pins} {k : Nat}
    (h0 : offset k = offset' k) (h1 : offset (k + 1) = offset' (k + 1))
    (st : Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1))) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset' budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset' budget p (k + 1)) := by
  intro x inv
  obtain ⟨fin, run, inv'⟩ := st x (inv_congr inv h0.symm)
  exact ⟨fin, run, inv_congr inv' h1⟩

/-- A guard CBZ at plan step k under offset function `off` (taken flag and decision explicit). -/
theorem brStep_cbz (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off : Nat → BitVec 64) (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (hereN : off k = HeapV2Compose.offsetOf k) (aligned : (off k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (Rt : BitVec 5) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (offk wordNat : Nat) (member : (offk, wordNat) ∈ HeapV2Plan.codeWords)
    (here : HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + offk))
    (wordEq : EntryBodyCbz.W Rt imm19 = BitVec.ofNat 32 wordNat)
    (land : off (k + 1) = if taken then HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64 else HeapV2Compose.offsetOf k + 4#64)
    (lowT : (base + (HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (dec : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x → (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ taken = true)) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k) (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins (k + 1)) :=
  HeapV2StepCerts.BranchStepV3.plan_step3_branch_cbz real spec config rows mapping _ HeapV2StepCerts.codeScope
    (HeapV2.image base) base static.separated base off budget pins k room hk page aligned upd0 Rt imm19 taken
    noEret dec
    (fun x inv => by rw [inv.v2.v1.pc, hereN, BitVec.add_assoc]; exact lowT)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, land]; cases taken <;> simp [BitVec.add_assoc])
    (fun x inv => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget k pins table static offk
      wordNat member here _ wordEq x (inv_congr inv hereN).v2)

/-- A guard B.cond at plan step k under offset function `off`. -/
theorem brStep_bcond (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off : Nat → BitVec 64) (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (hereN : off k = HeapV2Compose.offsetOf k) (aligned : (off k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (cond : BitVec 4) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (offk wordNat : Nat) (member : (offk, wordNat) ∈ HeapV2Plan.codeWords)
    (here : HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + offk))
    (wordEq : EntryBodyBcond.W cond imm19 = BitVec.ofNat 32 wordNat)
    (land : off (k + 1) = if taken then HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64 else HeapV2Compose.offsetOf k + 4#64)
    (lowT : (base + (HeapV2Compose.offsetOf k + sign_extend (imm19 ++ 0#2) 64)).toNat < 2 ^ 55)
    (dec : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k x → (Crypto.BcondCore.bcondC cond x.regs ↔ taken = true)) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins k) (ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base off budget pins (k + 1)) :=
  HeapV2StepCerts.BranchStepV3.plan_step3_branch_bcond real spec config rows mapping _ HeapV2StepCerts.codeScope
    (HeapV2.image base) base static.separated base off budget pins k room hk page aligned upd0 cond imm19 taken
    noEret dec
    (fun x inv => by rw [inv.v2.v1.pc, hereN, BitVec.add_assoc]; exact lowT)
    (fun x inv => by rw [inv.v2.v1.pc, hereN, land]; cases taken <;> simp [BitVec.add_assoc])
    (fun x inv => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget k pins table static offk
      wordNat member here _ wordEq x (inv_congr inv hereN).v2)

/-- Trap path 0 (HEAPV2-PATHS index 1, 1 step): guard branch k = 0 taken to certiffi_trap. -/
theorem trap0_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 1 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) :
    (∀ k, k ≤ 1 → ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 1) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 1).regs._PC = base + trapOffset := by
  have run := path_run3 real spec config rows mapping _ agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    (trapOff 1) budget pins 1 (by
        intro k hk
        have hk' : k = 0 := by omega
        rcases hk' with rfl
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 1) 0 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 0#5 179#19 true (by decide) 0 3019904608
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0)
    entry (inv_congr initial (by simp [trapOff]))
  refine ⟨run, ?_⟩
  have pc := (run 1 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 1 (HEAPV2-PATHS index 2, 2 steps): guard branch k = 1 taken to certiffi_trap. -/
theorem trap1_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 2 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) :
    (∀ k, k ≤ 2 → ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 2) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 2).regs._PC = base + trapOffset := by
  have run := path_run3 real spec config rows mapping _ agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    (trapOff 2) budget pins 2 (by
        intro k hk
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 2) 0 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 0#5 179#19 false (by decide) 0 3019904608
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 2) 1 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#5 178#19 true (by decide) 4 3019904577
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1)
    entry (inv_congr initial (by simp [trapOff]))
  refine ⟨run, ?_⟩
  have pc := (run 2 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 2 (HEAPV2-PATHS index 3, 4 steps): guard branch k = 3 taken to certiffi_trap. -/
theorem trap2_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 4 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) :
    (∀ k, k ≤ 4 → ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 4) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 4).regs._PC = base + trapOffset := by
  have run := path_run3 real spec config rows mapping _ agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    (trapOff 4) budget pins 4 (by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 4) 0 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 0#5 179#19 false (by decide) 0 3019904608
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 4) 1 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#5 178#19 false (by decide) 4 3019904577
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_2 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 4) 3 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 176#19 true (by decide) 12 1409291777
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3)
    entry (inv_congr initial (by simp [trapOff]))
  refine ⟨run, ?_⟩
  have pc := (run 4 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 3 (HEAPV2-PATHS index 4, 6 steps): guard branch k = 5 taken to certiffi_trap. -/
theorem trap3_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 6 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) :
    (∀ k, k ≤ 6 → ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 6) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 6).regs._PC = base + trapOffset := by
  have run := path_run3 real spec config rows mapping _ agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    (trapOff 6) budget pins 6 (by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 6) 0 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 0#5 179#19 false (by decide) 0 3019904608
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 6) 1 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#5 178#19 false (by decide) 4 3019904577
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_2 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 6) 3 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 176#19 false (by decide) 12 1409291777
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_4 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 6) 5 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 174#19 true (by decide) 20 1409291713
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5)
    entry (inv_congr initial (by simp [trapOff]))
  refine ⟨run, ?_⟩
  have pc := (run 6 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 4 (HEAPV2-PATHS index 5, 8 steps): guard branch k = 7 taken to certiffi_trap. -/
theorem trap4_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 8 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_7 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins 7 x →
      (Crypto.BcondCore.bcondC 3#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) :
    (∀ k, k ≤ 8 → ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 8) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 8).regs._PC = base + trapOffset := by
  have run := path_run3 real spec config rows mapping _ agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    (trapOff 8) budget pins 8 (by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 8) 0 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 0#5 179#19 false (by decide) 0 3019904608
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 8) 1 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#5 178#19 false (by decide) 4 3019904577
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_2 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 8) 3 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 176#19 false (by decide) 12 1409291777
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_4 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 8) 5 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 174#19 false (by decide) 20 1409291713
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_6 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 8) 7 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 3#4 172#19 true (by decide) 28 1409291651
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_7)
    entry (inv_congr initial (by simp [trapOff]))
  refine ⟨run, ?_⟩
  have pc := (run 8 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

/-- Trap path 5 (HEAPV2-PATHS index 6, 10 steps): guard branch k = 9 taken to certiffi_trap. -/
theorem trap5_run (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (HeapV2E17.consumerMap pins base.toNat mapping table))
    (room : 10 ≤ budget) (page : base.toNat % 4096 = 0)
    (low716 : (base + trapOffset).toNat < 2 ^ 55)
    (dec_0 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 0 x →
      (Crypto.CruxCbz.cbzC 1#1 0#5 x ↔ false = true))
    (dec_1 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 1 x →
      (Crypto.CruxCbz.cbzC 1#1 1#5 x ↔ false = true))
    (dec_3 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 3 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_5 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 5 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ false = true))
    (dec_7 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 7 x →
      (Crypto.BcondCore.bcondC 3#4 x.regs ↔ false = true))
    (dec_9 : ∀ x, ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins 9 x →
      (Crypto.BcondCore.bcondC 1#4 x.regs ↔ true = true))
    (entry : NativeState) (initial : ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry) :
    (∀ k, k ≤ 10 → ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) HeapV2StepCerts.codeScope (HeapV2.image base) base base (trapOff 10) budget pins k (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees (HeapV2E17.consumerMap pins base.toNat mapping table)
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry k)) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real entry 10).regs._PC = base + trapOffset := by
  have run := path_run3 real spec config rows mapping _ agrees HeapV2StepCerts.codeScope (HeapV2.image base) base base
    (trapOff 10) budget pins 10 (by
        intro k hk
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 10) 0 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 0#5 179#19 false (by decide) 0 3019904608
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_0
        · exact brStep_cbz real spec config rows mapping base budget pins table static (trapOff 10) 1 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#5 178#19 false (by decide) 4 3019904577
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_1
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_2 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 10) 3 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 176#19 false (by decide) 12 1409291777
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_3
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_4 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 10) 5 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 174#19 false (by decide) 20 1409291713
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_5
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_6 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 10) 7 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 3#4 172#19 false (by decide) 28 1409291651
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_7
        · exact step_congr real (by simp [trapOff]) (by simp [trapOff])
            (StraightV3.step3_8 real spec config rows mapping base budget pins table static (by omega) page)
        · exact brStep_bcond real spec config rows mapping base budget pins table static (trapOff 10) 9 (by omega) (by decide)
            page (by simp [trapOff]) (by decide +kernel) (by decide) 1#4 170#19 true (by decide) 36 1409291585
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by rw [show HeapV2Compose.offsetOf 9 + sign_extend (170#19 ++ 0#2) 64 = trapOffset by decide +kernel]; exact low716) dec_9)
    entry (inv_congr initial (by simp [trapOff]))
  refine ⟨run, ?_⟩
  have pc := (run 10 (Nat.le_refl _)).1.v2.v1.pc
  rw [pc]; simp [trapOff]

#print axioms inv_congr
#print axioms step_congr
#print axioms brStep_cbz
#print axioms brStep_bcond
#print axioms trap0_run
#print axioms trap1_run
#print axioms trap2_run
#print axioms trap3_run
#print axioms trap4_run
#print axioms trap5_run
end RtBl.Trap
