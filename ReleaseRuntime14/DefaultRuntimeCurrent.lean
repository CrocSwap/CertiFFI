-- Current-profile program invariant and runtime14 fetch obligations.
import DefaultCurrent
import PipeR14Mem.Physical.Inst
import PipeR14.FetchR14
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
namespace ReleaseProfile.DefaultRuntime
open PipeR14 ArmCertValue


structure InvG {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (extra : Nat → NativeState → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (capacity : Nat) (past : Nat → Nat) (k : Nat) (x : NativeState) : Prop where
  core : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x
  extra : extra k x
  statusRows : NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) capacity
  trace : ∃ used, NativeMteTagCheck.ChoiceDelta entry x used ∧ used ≤ past k

#check "CURRENT_DECL current_rows"
theorem current_rows {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget : Nat} {extra : Nat → NativeState → Prop} {catalogue : NativeMteTagCheck.ControlCatalogue}
    {entry x : NativeState} {capacity k cost : Nat} {past : Nat → Nat}
    (inv : InvG spec config rows mapping m scope image loadBase base offset budget extra catalogue entry capacity past k x)
    (room : past k + cost ≤ capacity) :
    NativeMteTagCheck.TagStatusRows x (x.choiceOcc.getD 1354 0) cost := by
  obtain ⟨used, delta, bound⟩ := inv.trace
  intro index within
  rw [delta.1, delta.2]
  simpa only [Nat.add_assoc] using inv.statusRows (used + index) (by omega)

#print axioms current_rows

abbrev InvPhysical {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List StepV)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvG spec config rows mapping m scope image loadBase base offset budget
    (ArmCertPipe.Physical.AgreesAt bytePA regions σ0 inputs plan) catalogue entry capacity past

#check "CURRENT_DECL fetchR14"
def fetchR14 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    {catalogue : NativeMteTagCheck.ControlCatalogue}
    {n : Nat} {accs : List R14E17.Access} {cws : List (Nat × Nat)} {entry : Nat} (hn : n < 14)
    (hcase : R14E17.caseMap n = some (accs, cws, entry)) {c : Nat × Nat} (member : c ∈ cws)
    (offset : Nat → BitVec 64) (budget k : Nat) (hoff : offset k = BitVec.ofNat 64 (entry + c.1))
    (x : NativeState)
    (inv : DefaultCurrent.CurrentInv spec config rows mapping (R14E17.consumerMap accs cws entry p base.toNat mapping table) sc
      (referenceImageI bytes base ifunc) base base offset budget k catalogue x) :
    FetchObligations spec config rows mapping (BitVec.ofNat 32 c.2) x :=
  have mv := R14E17.mem_codeVAs hn hcase member
  have pcImage : x.regs._PC = MemReloc.imageAddress base (entry + c.1) := by
    rw [inv.v1.pc, hoff]; rfl
  DefaultCurrent.fetchG spec config rows mapping _ sc (referenceImageI bytes base ifunc) base base offset budget k catalogue x
    inv (entry + c.1) (BitVec.ofNat 32 c.2) pcImage (inside_of_mem cs.covers mv) (cs.contiguous _ mv) (cs.notMMIO _ mv)
    cs.separated (R14E17.case_code_image bytes b cb base ifunc hn hcase member)
    (fun acc shape => Or.inr ⟨c, member, by
      rw [pcImage]; apply BitVec.eq_of_toNat_eq
      simp only [MemReloc.imageAddress, R14E17.codeVA, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega, rfl, shape⟩)

abbrev Inv_c00 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c00 R14Plan.codeWords_c00 R14Plan.entry_c00 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c00 budget bytePA regions_c00 σ0_c00 inputs plan_c00 catalogue entry capacity past

abbrev Inv_c01 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c01 R14Plan.codeWords_c01 R14Plan.entry_c01 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c01 budget bytePA regions_c01 σ0_c01 inputs plan_c01 catalogue entry capacity past

abbrev Inv_c02 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c02 R14Plan.codeWords_c02 R14Plan.entry_c02 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c02 budget bytePA regions_c02 σ0_c02 inputs plan_c02 catalogue entry capacity past

abbrev Inv_c03 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c03 R14Plan.codeWords_c03 R14Plan.entry_c03 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c03 budget bytePA regions_c03 σ0_c03 inputs plan_c03 catalogue entry capacity past

abbrev Inv_c04 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c04 R14Plan.codeWords_c04 R14Plan.entry_c04 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c04 budget bytePA regions_c04 σ0_c04 inputs plan_c04 catalogue entry capacity past

abbrev Inv_c05 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c05 budget bytePA regions_c05 σ0_c05 inputs plan_c05 catalogue entry capacity past

abbrev Inv_c06 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c06 budget bytePA regions_c06 σ0_c06 inputs plan_c06 catalogue entry capacity past

abbrev Inv_c07 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c07 budget bytePA regions_c07 σ0_c07 inputs plan_c07 catalogue entry capacity past

abbrev Inv_c08 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c08 budget bytePA regions_c08 σ0_c08 inputs plan_c08 catalogue entry capacity past

abbrev Inv_c09 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c09 R14Plan.codeWords_c09 R14Plan.entry_c09 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c09 budget bytePA regions_c09 σ0_c09 inputs plan_c09 catalogue entry capacity past

abbrev Inv_c10 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c10 R14Plan.codeWords_c10 R14Plan.entry_c10 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c10 budget bytePA regions_c10 σ0_c10 inputs plan_c10 catalogue entry capacity past

abbrev Inv_c11 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c11 R14Plan.codeWords_c11 R14Plan.entry_c11 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c11 budget bytePA regions_c11 σ0_c11 inputs plan_c11 catalogue entry capacity past

abbrev Inv_c12 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c12 budget bytePA regions_c12 σ0_c12 inputs plan_c12 catalogue entry capacity past

abbrev Inv_c13 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (past : Nat → Nat) : Nat → NativeState → Prop :=
  InvPhysical spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c13 R14Plan.codeWords_c13 R14Plan.entry_c13 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c13 budget bytePA regions_c13 σ0_c13 inputs plan_c13 catalogue entry capacity past

#print axioms fetchR14
#print axioms InvPhysical
end ReleaseProfile.DefaultRuntime
