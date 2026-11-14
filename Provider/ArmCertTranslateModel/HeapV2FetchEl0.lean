import ArmCertTranslateModel.HeapV2Fetch
import ArmCertWalk.IFetchElSs

/-! `fetch_per_acc` with the IFETCH descriptor's EL/SS derived from the before-fetch
registers (Memory `actual_ifetch_el_ss`), so no descriptor-shape hypothesis remains. The
register facts are ones Core's ChainInv already carries (StepPins/EntryFeatures/host). -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model.HeapV2E17

theorem fetch_per_acc_el0 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (p : Pins) (base : Nat) (table : Nat → Prop) {pre : State} {code : Nat × Nat}
    (member : code ∈ HeapV2Plan.codeWords) (pcAt : pre.regs._PC = codeVA base code.1)
    (closed : ClosedMembershipAt spec config rows mapping (consumerMap p base mapping table) pre)
    (noRME : pre.regs.FeatureImpl[232] = false) (a64 : pre.regs.PSTATE.nRW = 0#1)
    (el3a64 : pre.regs.FeatureImpl[7] = true) (noEl3a32 : pre.regs.FeatureImpl[3] = false)
    (el : pre.regs.PSTATE.EL = 0#2)
    (ns : Sail.BitVec.extractLsb (pre.regs.bank_BitVec_64 .SCR_EL3) 0 0 = 1#1) :
    ∀ acc, ActualIFetchAcc pre acc →
      domain ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩,
        CurrentS1AccessAt spec config rows mapping ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ data pre :=
  fetch_per_acc spec config rows mapping p base table member pcAt closed
    (fun _ actual => actual_ifetch_el_ss actual noRME a64 el3a64 noEl3a32 el ns)

#print axioms fetch_per_acc_el0
end ArmCert.Translate.Model.HeapV2E17
