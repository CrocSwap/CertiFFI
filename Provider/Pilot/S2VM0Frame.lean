import Pilot.S2VM0
import Pilot.S2Interface
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2VM0Frame
abbrev State := S2Interface.State

def faultOut (fault : FaultRecord) (ipa : AddressDescriptor) (acc : AccessDescriptor) : FaultRecord :=
  {fault with
    statuscode := .Fault_None
    secondstage := true
    s2fs1walk := acc.acctype == .AccessType_TTW
    ipaddress := ipa.paddress}

def Effect (fault : FaultRecord) (ipa : AddressDescriptor) (acc : AccessDescriptor) (s : State) :
    EStateM.Result (Sail.Error exception) State (FaultRecord × AddressDescriptor) → Prop
  | .ok (f, a) t => f = faultOut fault ipa acc ∧ a = ipa ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events
  | .error _ _ => False

theorem native_effect (c : S2Interface.Config) (fault : FaultRecord) (ipa : AddressDescriptor)
    (a64 : Bool) (level : Option Int) (aligned : Bool) (acc : AccessDescriptor) (s : State) :
    Effect fault ipa acc s
      (S2VM0.native c.hcr c.vtcr c.sctlr c.hcrx c.s2pir c.scr c.vttbrLow c.vttbr
        fault ipa a64 level aligned acc s) := by
  delta S2VM0.native
  simp [Effect, faultOut]

theorem total (c : S2Interface.Config) (fault : FaultRecord) (ipa : AddressDescriptor)
    (a64 : Bool) (level : Option Int) (aligned : Bool) (acc : AccessDescriptor) (s : State)
    (hconfig : S2Interface.ConfigAt c s)
    (hVM : _get_HCR_EL2_Type_VM c.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC c.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure) :
    ∃ t : State,
      AArch64_S2Translate fault ipa a64 level aligned acc s = .ok (faultOut fault ipa acc, ipa) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  have he : Effect fault ipa acc s (AArch64_S2Translate fault ipa a64 level aligned acc s) := by
    rw [S2VM0.complete c.hcr c.vtcr c.sctlr c.hcrx c.s2pir c.scr c.vttbrLow c.vttbr
      fault ipa a64 level aligned acc s hconfig.hHCR hconfig.hVTCR hconfig.hSCTLR
      hconfig.hHCRX hconfig.hS2PIR hconfig.hSCR hconfig.hVTTBR hconfig.hVTTBRLow
      (S2VM0.vm_field c.hcr hVM) (S2VM0.dc_field c.hcr hDC) hSS]
    exact native_effect c fault ipa a64 level aligned acc s
  cases hr : AArch64_S2Translate fault ipa a64 level aligned acc s with
  | error err t => simp only [hr, Effect] at he
  | ok pair t =>
    rcases pair with ⟨f, a⟩
    simp only [hr, Effect] at he
    rcases he with ⟨hf, ha, hregs, hmem, hevents⟩
    subst f; subst a
    exact ⟨t, rfl, hregs, hmem, hevents⟩

@[simp] theorem status (fault : FaultRecord) (ipa : AddressDescriptor) (acc : AccessDescriptor) :
    (faultOut fault ipa acc).statuscode = .Fault_None := rfl
#print axioms total
end S2VM0Frame
