-- Memory: the epilogue LDP x19, x30 at k = 354 as a rich step whose payload is
-- LdpPay2 (both halves), so the residue's RtSaved3.LrField gets X19 back (field_ldp354).
import HeapV2StepCerts.AccShape
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.BodyMemD
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemRunD
import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.MemStepsV3
import HeapV2StepCerts.MemStepsV3_00
import HeapV2StepCerts.MemStepsV3_01
import HeapV2StepCerts.MemStepsV3_02
import HeapV2StepCerts.MemStepsV3_03
import HeapV2StepCerts.MemStepsV3_04
import HeapV2StepCerts.MemStepsV3_05
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.MemTailLdrb
import HeapV2StepCerts.MemTailPair
import HeapV2StepCerts.MemTailStrb
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.Straight
import HeapV2StepCerts.StraightV2
import HeapV2StepCerts.ValueTailDef
import HeapV2StepCerts.MemStepsV4_05
import RtS3.MemFacts2
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace HeapV2StepCerts

theorem memStep4_354L (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (dataStatic : C3.DataStatic pins mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0)
    (codeD : ImageTableSeparated codeScope base mapping (MemNext.dataBytes pins mapping))
    (room : 354 < budget) (page : base.toNat % 4096 = 0) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 354)
      (ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (354 + 1)) (MemNext.MemR 354 (fun _ => False) (RtSaved3.MemFacts2.LdpPay2 pins mapping (354, 0, (-16), 16, false) (19#5) (30#5))) :=
  MemNext.plan_step4_mem real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 354 room (by decide) page (by decide +kernel)
    (fun _ => False) (fun _ _ _ _ h => h) (RtSaved3.MemFacts2.LdpPay2 pins mapping (354, 0, (-16), 16, false) (19#5) (30#5)) (fun _ _ _ _ m h => RtSaved3.MemFacts2.LdpPay2.transport m h) (by decide +kernel)
    (NativeEntryBodyDispatch.Ldp.selected (19#5) (30#5) (6#7)) NativeEntryBodyMem.Ldp.writes 611
    (fun x => x.regs._PC + 4#64)
    (fun x _ => RtSaved3.MemFacts2.memVP_Ldp2 real spec config rows mapping dataStatic pinAligned (MemSteps.step_354).1 rfl (6#7) (19#5) (30#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_354).2.1 (MemSteps.step_354).2.2.2.1 (MemSteps.step_354).2.2.2.2 rfl rfl (MemSteps.step_354).2.2.1 x)
    (fun x inv => MemNext.memNextPlaced spec config rows mapping base budget 354 pins table static 0xb4 0xa9437bf3
      (by decide +kernel) (by decide +kernel) (by decide +kernel) x inv.v2)
    (fun x inv => MemNext.memFetch spec config rows mapping base budget 354 pins table static 0xb4 0xa9437bf3
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp.selected (19#5) (30#5) (6#7)) (by decide +kernel) x inv.v2)

#print axioms memStep4_354L
end HeapV2StepCerts
