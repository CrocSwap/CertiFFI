-- Memory: E17 for an ARBITRARY heap-v2 deployment. The premise bundle, the ChainInv v4 instance and
-- the step-0 invariant; the per-step segments are certiffi's E17Synth assembly with the synthetic constants replaced.
-- own modules the Core / step lemmas import HeapV2StepCerts.AccShape
import HeapV2StepCerts.AccShape
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.FlagRoots
import HeapV2StepCerts.FlagTails
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemRunD
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.MemStepsV3_00
import HeapV2StepCerts.MemStepsV3_01
import HeapV2StepCerts.MemStepsV3_02
import HeapV2StepCerts.MemStepsV3_03
import HeapV2StepCerts.MemStepsV3_04
import HeapV2StepCerts.MemStepsV3_05
import HeapV2StepCerts.MemTailLdrb
import HeapV2StepCerts.MemTailStrb
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegRootsB
import HeapV2StepCerts.Straight
import HeapV2StepCerts.StraightV2
import HeapV2StepCerts.ValBindCore
import HeapV2StepCerts.ValBindData
import HeapV2StepCerts.ValueTailDef
import HeapV2StepCerts.BodyMemD
import HeapV2StepCerts.BranchFrame
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.Carry
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemStepsV3
import HeapV2StepCerts.MemStepsV4_00
import HeapV2StepCerts.MemStepsV4_01
import HeapV2StepCerts.MemStepsV4_02
import HeapV2StepCerts.MemStepsV4_03
import HeapV2StepCerts.MemStepsV4_04
import HeapV2StepCerts.MemStepsV4_05
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.MemTailPair
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.RegValSteps00
import HeapV2StepCerts.RegValSteps01
import HeapV2StepCerts.RegValSteps02
import HeapV2StepCerts.RegValSteps03
import HeapV2StepCerts.RegValSteps04
import HeapV2StepCerts.RegValSteps05
import HeapV2StepCerts.StepsV2_00
import HeapV2StepCerts.StepsV2_01
import HeapV2StepCerts.StepsV2_02
import HeapV2StepCerts.StepsV2_03
import HeapV2StepCerts.StepsV2_04
import HeapV2StepCerts.StepsV2_05
import HeapV2StepCerts.TailW
import HeapV2StepCerts.TailWStepsC0
import HeapV2StepCerts.TailWStepsC1
import HeapV2StepCerts.TailWStepsC2
import HeapV2StepCerts.TailWStepsC3
import HeapV2StepCerts.TailWStepsC4
import HeapV2StepCerts.TailWStepsC5
import HeapV2StepCerts.TailWStepsC6
import HeapV2StepCerts.TailWStepsC7a
import HeapV2StepCerts.TailWStepsC7b
import HeapV2StepCerts.TailWStepsC7c
import HeapV2StepCerts.TailWStepsC7d
import HeapV2StepCerts.ValBind
import HeapV2StepCerts.ValBindDec
import HeapV2StepCerts.ValBindSteps00
import HeapV2StepCerts.ValBindSteps01
import HeapV2StepCerts.ValBindSteps02
import HeapV2StepCerts.ValBindSteps03
import HeapV2StepCerts.ValBindSteps04
import HeapV2StepCerts.ValBindSteps05
import HeapV2StepCerts.MemNextV4
import HeapV2StepCerts.CodeData
import Bridge.CruxGenGuarded.ChainInvV4At
import RtS2.Link
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.E17General
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-- Value inputs: the entry X2/X3. -/
def qOf (entry : NativeState) : HeapV2StepCerts.ValBind.Inputs :=
  ⟨HeapV2StepCerts.RegBind.regVal entry (.x 2), HeapV2StepCerts.RegBind.regVal entry (.x 3)⟩

/-- The table footprint consumerMap of a deployment. -/
abbrev cmap {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  HeapV2E17.consumerMap pins base.toNat mapping (rowsFootprint spec.imageRows).byte

/-- Everything a heap-v2 deployment must satisfy for E17 on the normal path. Static deployment checks
(all Boolean in practice: codeStatic_of_checks, DataStatic, codeD_of_check, slotSep_of_check), the load-base bounds,
the consumer-map agreement, the path-0 input condition, and the step-0 invariant at the entry state. -/
structure DeploymentPremises {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) : Prop where
  static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte
  dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows)
  pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0
  codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping)
  sep : RtSaved.SlotSep pins mapping
  mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping (cmap spec mapping base pins)
  np : HeapV2StepCerts.ValBind.NormalPath pins (qOf entry)
  /-- ChainInv3 at the entry, at THIS budget (: budget-bounded end to end, init3 v2 / E23). -/
  init3 : ChainInvV3.ChainInv3 spec config rows mapping (cmap spec mapping base pins) HeapV2StepCerts.codeScope
    (HeapV2.image base) base base HeapV2Compose.offsetOf budget pins 0 entry
  /-- The logical rows' VAs are distinct (/ FetchTiming: the no-update walk's records are a function of (spec, VA)). -/
  nodup : (spec.logicalRows.map (·.logical)).Nodup
  residue : RtBl.CallerInv.CallerResidue entry

/-- ChainInv v4 on the deployment, seeded with the entry's X19/X30. -/
abbrev I4 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat) (x : NativeState) : Prop :=
  ChainInv4 spec config rows mapping (cmap spec mapping base pins) HeapV2StepCerts.codeScope (HeapV2.image base) base base
    HeapV2Compose.offsetOf budget pins (qOf entry) (entry.regs.gpr[19]) (entry.regs.gpr[30]) k x

def memKs : List Nat := [11, 18, 19, 22, 23, 26, 27, 30, 31, 34, 35, 38, 39, 42, 43, 46, 47, 50, 51, 54, 55, 58, 59, 62, 63, 66, 67, 70, 71, 74, 75, 78, 79, 82, 83, 86, 87, 90, 91, 94, 95, 98, 99, 102, 103, 106, 107, 110, 111, 114, 115, 118, 119, 122, 123, 126, 127, 130, 131, 134, 135, 138, 139, 142, 143, 153, 156, 159, 162, 165, 168, 171, 174, 177, 180, 183, 186, 189, 192, 195, 198, 201, 204, 207, 210, 213, 216, 219, 222, 225, 228, 231, 234, 237, 240, 243, 246, 253, 256, 329, 330, 351, 352, 353, 354, 355]

def isMem (k : Nat) : Bool := memKs.contains k

def MemStepsG (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) : Prop :=
  ∀ k, k < 357 → isMem k = true →
    Uget.Chain.Step real (I4 spec config rows mapping base pins entry budget k) (I4 spec config rows mapping base pins entry budget (k + 1))

/-- A branch / call target bound from the load-base bound (every plan offset is below 2^20). -/
theorem low_of {base : BitVec 64} (c : BitVec 64) (hc : c.toNat < 2 ^ 20) (hb : base.toNat < 2 ^ 54) :
    (base + c).toNat < 2 ^ 55 := by
  rw [BitVec.toNat_add]; omega

theorem initialG {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} {entry : NativeState}
    (budget : Nat) (dp : DeploymentPremises spec config rows mapping base pins entry budget) :
    I4 spec config rows mapping base pins entry budget 0 entry :=
  ⟨dp.init3, HeapV2StepCerts.ValBind.initial _, RtSaved2.field_zero _, dp.residue⟩

#print axioms low_of
#print axioms initialG
end HeapV2StepCerts.E17General
