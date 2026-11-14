import ArmCertPipe.ChainInvG
import ArmCertLoop.Image
import ArmCertLoop.Generated
import ArmCertLoop.Schedule
import CertiFFIClaim.Kinds
import ArmCertTranslateModel.StaticPieScoped

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft
open ArmBridge.CruxGenGuarded.EntryClassNext
open HeapV2StepCerts.RegBind (Reg St regVal)
open CertiFFI.Claim

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.ContractDraft

/-! PROPOSED TYPES, NOT CERTIFICATES. These definitions describe the public
memcpy proposition intended for independent exact positive-policy review.
There is no proof of memcpyClaim, no admitted declaration, no C1/C2 target,
and no public admission. Native block/cutpoint/progress callbacks do not occur
in its premises. All deployment facts concern addresses or ONE actual entry.
The canonical byte native routes are not yet integrated. -/

def sourceSpan (s : BitVec 64) (n : Nat) : SpanMap.Span := ⟨s, n, false⟩
def destSpan (d : BitVec 64) (n : Nat) : SpanMap.Span := ⟨d, n, true⟩
def spans (d s : BitVec 64) (n : Nat) : List SpanMap.Span := [sourceSpan s n, destSpan d n]

def codeScope (off : Nat) : Prop :=
  Generated.imageStart ≤ off ∧ off < Generated.imageStart + 4 * Generated.imageWords.length

def image : MemReloc.Image := Image.wordImage Generated.imageStart Generated.imageWords

/-- Exact file-offset binding for this pinned static-PIE text layout. The
generator rejects gaps; this ELF has text file offsets equal to link VAs.
Array bounds and all four bytes of every instruction are checked. -/
def CodeBytesBound (bytes : Array Nat) : Prop :=
  Generated.imageStart + 4 * Generated.imageWords.length ≤ bytes.size ∧
  ∀ i, i < Generated.imageWords.length → ∀ k, k < 4 →
    bytes[Generated.imageStart + 4 * i + k]? =
      some (((Generated.imageWords.getD i 0).extractLsb' (8 * k) 8).toNat)

def consumer (mapping : BitVec 64 → Option Nat) (base d s : BitVec 64) (n : Nat)
    (tables : Nat → Prop) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  SpanMap.consumerMap (spans d s n) (Image.codeVAs base Generated.imageStart Generated.imageWords) mapping tables

def offset (base returnPC : BitVec 64) (n : Nat) : Nat → BitVec 64 :=
  Schedule.nativeOffset base returnPC (Schedule.copySteps n)
    (fun k => Generated.armcert_memcpy_entry + Schedule.copyWordOffset n k)

def readByte (mapping : BitVec 64 → Option Nat) (entry : NativeState) (va : BitVec 64) :
    Option (BitVec 8) := (mapping va).bind fun pa => entry.mem[pa]?

def Args (d s returnPC : BitVec 64) (n : Nat) (entry : NativeState) : Prop :=
  regVal entry (.x 0) = d ∧ regVal entry (.x 1) = s ∧
  (regVal entry (.x 2)).toNat = n ∧ regVal entry (.x 30) = returnPC

def SourcePresent (mapping : BitVec 64 → Option Nat) (s : BitVec 64) (n : Nat) (entry : NativeState) : Prop :=
  ∀ i, i < n → ∃ b, readByte mapping entry (s + BitVec.ofNat 64 i) = some b

def DestinationPA (mapping : BitVec 64 → Option Nat) (d : BitVec 64) (n pa : Nat) : Prop :=
  ∃ i, i < n ∧ mapping (d + BitVec.ofNat 64 i) = some pa

def CopyPost (mapping : BitVec 64 → Option Nat) (d s returnPC : BitVec 64) (n : Nat)
    (entry fin : NativeState) : Prop :=
  fin.regs._PC = returnPC ∧ regVal fin (.x 0) = d ∧
  (∀ i, i < n → readByte mapping fin (d + BitVec.ofNat 64 i) =
    readByte mapping entry (s + BitVec.ofNat 64 i)) ∧
  (∀ pa, ¬ DestinationPA mapping d n pa → fin.mem[pa]? = entry.mem[pa]?) ∧
  (∀ r : Fin 31, 6 ≤ r.val → regVal fin (.x r) = regVal entry (.x r)) ∧
  fin.regs.SP_EL0 = entry.regs.SP_EL0 ∧ fin.regs._Z = entry.regs._Z ∧
  ArmFull.Register.FPCR.get fin.regs = ArmFull.Register.FPCR.get entry.regs ∧
  ArmFull.Register.FPSR.get fin.regs = ArmFull.Register.FPSR.get entry.regs

/-- Static code geometry only, independent of machine state and payloads. -/
def CodeGeometry (mapping : BitVec 64 → Option Nat) (base : BitVec 64) : Prop :=
  ∀ i, i < Generated.imageWords.length →
    ImageWordContiguous mapping base (Generated.imageStart + 4 * i) ∧
    MappedNotMMIO mapping (MemReloc.imageAddress base (Generated.imageStart + 4 * i))

/-- Data mapping/RAM/table isolation at exactly the byte addresses accessed.
There is no word padding, physical contiguity or future-state duty here. -/
def DataGeometry (mapping : BitVec 64 → Option Nat) (d s : BitVec 64) (n : Nat)
    (tables : Nat → Prop) : Prop :=
  ∀ span ∈ spans d s n, ∀ i, i < span.length →
    ∃ pa : BitVec 56, mapping (SpanMap.byteVA span i) = some pa.toNat ∧
      MemM1.MemReadIF.NotMMIO pa ∧ ¬ tables pa.toNat

/-- Destination physical bytes cannot alias any bound instruction byte. Source
may overlap read-only code if the remaining profile permits that read. -/
def CodeWriteSeparated (mapping : BitVec 64 → Option Nat) (base d : BitVec 64) (n : Nat) : Prop :=
  ∀ off, codeScope off → ∀ pa, mapping (MemReloc.imageAddress base off) = some pa →
    ¬ DestinationPA mapping d n pa

/-- Proposed complete memcpy proposition. A theorem proving this type will
only be exported after all native callbacks are internally derived, exact
positive-policy approval and actual closed C2 witnesses. -/
def memcpyClaim (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (bytes : Array Nat) (base d s returnPC : BitVec 64) (n : Nat) (entry : NativeState) : Prop :=
  RunCheck "loop:code-bytes-bound" (CodeBytesBound bytes) →
  RunCheck "loop:relocations-empty" (ArmCert.Translate.Model.StaticPie.relaTable bytes = some []) →
  CallerContract "loop:memcpy:args" (Args d s returnPC n entry) →
  CallerContract "loop:memcpy:source-object" (SpanMap.NoWrap (sourceSpan s n)) →
  CallerContract "loop:memcpy:destination-object" (SpanMap.NoWrap (destSpan d n)) →
  CallerContract "loop:memcpy:disjoint" (d.toNat + n ≤ s.toNat ∨ s.toNat + n ≤ d.toNat) →
  CallerContract "loop:memcpy:source-present" (SourcePresent mapping s n entry) →
  CallerContract "loop:return-canonical" (returnPC.toNat < 2 ^ 54) →
  DeploymentObligation "loop:load-base-page" (base.toNat % 4096 = 0) →
  DeploymentObligation "loop:load-base-low" (base.toNat < 2 ^ 54) →
  DeploymentObligation "loop:code-geometry" (CodeGeometry mapping base) →
  DeploymentObligation "loop:code-write-separated" (CodeWriteSeparated mapping base d n) →
  DeploymentObligation "loop:data-geometry"
    (DataGeometry mapping d s n (rowsFootprint spec.imageRows).byte) →
  DeploymentObligation "loop:union-injective" (SpanMap.UnionInjective mapping (spans d s n)) →
  DeploymentObligation "loop:image-table-separated"
    (ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte) →
  DeploymentObligation "loop:consumer-map-agrees"
    (ConsumerMapAgrees spec mapping (consumer mapping base d s n (rowsFootprint spec.imageRows).byte)) →
  DeploymentObligation "loop:entry-context"
    (ArmCertPipe.ChainInvG spec config rows mapping
      (consumer mapping base d s n (rowsFootprint spec.imageRows).byte)
      codeScope image base base (offset base returnPC n) (Schedule.copySteps n)
      (fun _ _ => True) 0 entry) →
  ∃ ticks fin, ticks ≤ Schedule.copySteps n ∧
    Uget.Chain.modelRun real ticks entry = .ok () fin ∧ CopyPost mapping d s returnPC n entry fin

#print axioms memcpyClaim
#print axioms CopyPost
#print axioms DataGeometry

end ArmCertLoop.ContractDraft
