import DefaultRuntimeC00Run
import DefaultRuntimeC01Run
import DefaultRuntimeC02Run
import DefaultRuntimeC03Run
import DefaultRuntimeC04Run
import DefaultRuntimeC05Run
import DefaultRuntimeC06Run
import DefaultRuntimeC07Run
import DefaultRuntimeC08Run
import DefaultRuntimeC09Run
import DefaultRuntimeC10Run
import DefaultRuntimeC11Run
import DefaultRuntimeC12Run
import DefaultRuntimeC13Run

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate.Model.StaticPie
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-!
# Runtime fetch coverage

For each case, `fetch_covered_cNN` has exactly the hypotheses of `run_cNN`. It states that the PC of every state the
certified run fetches from, `stateAt real entry k` for `k < plan_cNN.length`, is the load base plus a
reviewed code word of the case: `R14Plan.entry_cNN + c.1` for some `c ∈ R14Plan.codeWords_cNN`. Those words
are the bytes of `RuntimeImage.reviewedImageBytes`. The proof is the invariant PC field of `run_cNN`
(`ChainInv.pc : _PC = base + offset k`) plus a decided check that each `offset_cNN k` is a code word.
The PC after the run is `finpc_dp_cNN`: the caller LR (RET) for c00-c07, and a pinned stop word for c08-c13.
-/

namespace ReleaseProfile.DefaultRuntime
open PipeR14 PipeR14.Physical

/-- Static: every planned PC of case c00 is a reviewed code word of the case. -/
theorem pcs_reviewed_c00 : (List.range plan_c00.length).all (fun k => R14Plan.codeWords_c00.any
    (fun c => decide (offset_c00 k = BitVec.ofNat 64 (R14Plan.entry_c00 + c.1)))) = true := by decide

/-- **Every PC fetched by run c00 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c00) (hpath : ArmCertPipe.PathOK (extend inputs D_c00) guards_c00) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c00 regions_c00 sc base) (hp : PinsAgree p rs_c00 forms_c00 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c00.length ≤ budget)
    (entry : NativeState)
    (init : ReleaseProfile.DefaultRuntime.Inv_c00 spec config rows mapping
      table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c00 past_c00 0 entry) :
    ∀ k, k < plan_c00.length → ∃ c ∈ R14Plan.codeWords_c00,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c00 + c.1) := by
  intro k hk
  have hpc := ((run_c00 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c00 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c01 is a reviewed code word of the case. -/
theorem pcs_reviewed_c01 : (List.range plan_c01.length).all (fun k => R14Plan.codeWords_c01.any
    (fun c => decide (offset_c01 k = BitVec.ofNat 64 (R14Plan.entry_c01 + c.1)))) = true := by decide

/-- **Every PC fetched by run c01 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c01) (hpath : ArmCertPipe.PathOK (extend inputs D_c01) guards_c01) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c01 regions_c01 sc base) (hp : PinsAgree p rs_c01 forms_c01 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c01.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c01 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c01 past_c01 0 entry) :
    ∀ k, k < plan_c01.length → ∃ c ∈ R14Plan.codeWords_c01,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c01 + c.1) := by
  intro k hk
  have hpc := ((run_c01 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c01 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c02 is a reviewed code word of the case. -/
theorem pcs_reviewed_c02 : (List.range plan_c02.length).all (fun k => R14Plan.codeWords_c02.any
    (fun c => decide (offset_c02 k = BitVec.ofNat 64 (R14Plan.entry_c02 + c.1)))) = true := by decide

/-- **Every PC fetched by run c02 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c02) (hpath : ArmCertPipe.PathOK (extend inputs D_c02) guards_c02) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c02 regions_c02 sc base) (hp : PinsAgree p rs_c02 forms_c02 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c02.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c02 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c02 past_c02 0 entry) :
    ∀ k, k < plan_c02.length → ∃ c ∈ R14Plan.codeWords_c02,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c02 + c.1) := by
  intro k hk
  have hpc := ((run_c02 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c02 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c03 is a reviewed code word of the case. -/
theorem pcs_reviewed_c03 : (List.range plan_c03.length).all (fun k => R14Plan.codeWords_c03.any
    (fun c => decide (offset_c03 k = BitVec.ofNat 64 (R14Plan.entry_c03 + c.1)))) = true := by decide

/-- **Every PC fetched by run c03 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c03 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c03) (hpath : ArmCertPipe.PathOK (extend inputs D_c03) guards_c03) (hlr : (inputs.getD 83 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c03 regions_c03 sc base) (hp : PinsAgree p rs_c03 forms_c03 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c03.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c03 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c03 past_c03 0 entry) :
    ∀ k, k < plan_c03.length → ∃ c ∈ R14Plan.codeWords_c03,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c03 + c.1) := by
  intro k hk
  have hpc := ((run_c03 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c03 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c04 is a reviewed code word of the case. -/
theorem pcs_reviewed_c04 : (List.range plan_c04.length).all (fun k => R14Plan.codeWords_c04.any
    (fun c => decide (offset_c04 k = BitVec.ofNat 64 (R14Plan.entry_c04 + c.1)))) = true := by decide

/-- **Every PC fetched by run c04 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c04) (hpath : ArmCertPipe.PathOK (extend inputs D_c04) guards_c04) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c04 regions_c04 sc base) (hp : PinsAgree p rs_c04 forms_c04 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c04.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c04 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c04 past_c04 0 entry) :
    ∀ k, k < plan_c04.length → ∃ c ∈ R14Plan.codeWords_c04,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c04 + c.1) := by
  intro k hk
  have hpc := ((run_c04 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c04 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c05 is a reviewed code word of the case. -/
theorem pcs_reviewed_c05 : (List.range plan_c05.length).all (fun k => R14Plan.codeWords_c05.any
    (fun c => decide (offset_c05 k = BitVec.ofNat 64 (R14Plan.entry_c05 + c.1)))) = true := by decide

/-- **Every PC fetched by run c05 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c05) (hpath : ArmCertPipe.PathOK (extend inputs D_c05) guards_c05) (hlr : (inputs.getD 71 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c05 regions_c05 sc base) (hp : PinsAgree p rs_c05 forms_c05 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c05.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c05 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c05 past_c05 0 entry) :
    ∀ k, k < plan_c05.length → ∃ c ∈ R14Plan.codeWords_c05,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c05 + c.1) := by
  intro k hk
  have hpc := ((run_c05 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c05 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c06 is a reviewed code word of the case. -/
theorem pcs_reviewed_c06 : (List.range plan_c06.length).all (fun k => R14Plan.codeWords_c06.any
    (fun c => decide (offset_c06 k = BitVec.ofNat 64 (R14Plan.entry_c06 + c.1)))) = true := by decide

/-- **Every PC fetched by run c06 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c06 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c06) (hpath : ArmCertPipe.PathOK (extend inputs D_c06) guards_c06) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c06 regions_c06 sc base) (hp : PinsAgree p rs_c06 forms_c06 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c06.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c06 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c06 past_c06 0 entry) :
    ∀ k, k < plan_c06.length → ∃ c ∈ R14Plan.codeWords_c06,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c06 + c.1) := by
  intro k hk
  have hpc := ((run_c06 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c06 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c07 is a reviewed code word of the case. -/
theorem pcs_reviewed_c07 : (List.range plan_c07.length).all (fun k => R14Plan.codeWords_c07.any
    (fun c => decide (offset_c07 k = BitVec.ofNat 64 (R14Plan.entry_c07 + c.1)))) = true := by decide

/-- **Every PC fetched by run c07 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c07) (hpath : ArmCertPipe.PathOK (extend inputs D_c07) guards_c07) (hlr : (inputs.getD 99 0).toNat < 2 ^ 54)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c07 regions_c07 sc base) (hp : PinsAgree p rs_c07 forms_c07 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c07.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c07 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c07 past_c07 0 entry) :
    ∀ k, k < plan_c07.length → ∃ c ∈ R14Plan.codeWords_c07,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c07 + c.1) := by
  intro k hk
  have hpc := ((run_c07 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath hlr ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c07 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c08 is a reviewed code word of the case. -/
theorem pcs_reviewed_c08 : (List.range plan_c08.length).all (fun k => R14Plan.codeWords_c08.any
    (fun c => decide (offset_c08 k = BitVec.ofNat 64 (R14Plan.entry_c08 + c.1)))) = true := by decide

/-- **Every PC fetched by run c08 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c08) (hpath : ArmCertPipe.PathOK (extend inputs D_c08) guards_c08)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c08.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c08 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c08 past_c08 0 entry) :
    ∀ k, k < plan_c08.length → ∃ c ∈ R14Plan.codeWords_c08,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c08 + c.1) := by
  intro k hk
  have hpc := ((run_c08 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c08 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c09 is a reviewed code word of the case. -/
theorem pcs_reviewed_c09 : (List.range plan_c09.length).all (fun k => R14Plan.codeWords_c09.any
    (fun c => decide (offset_c09 k = BitVec.ofNat 64 (R14Plan.entry_c09 + c.1)))) = true := by decide

/-- **Every PC fetched by run c09 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c09) (hpath : ArmCertPipe.PathOK (extend inputs D_c09) guards_c09)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c09 regions_c09 sc base) (hp : PinsAgree p rs_c09 forms_c09 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c09.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c09 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c09 past_c09 0 entry) :
    ∀ k, k < plan_c09.length → ∃ c ∈ R14Plan.codeWords_c09,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c09 + c.1) := by
  intro k hk
  have hpc := ((run_c09 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c09 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c10 is a reviewed code word of the case. -/
theorem pcs_reviewed_c10 : (List.range plan_c10.length).all (fun k => R14Plan.codeWords_c10.any
    (fun c => decide (offset_c10 k = BitVec.ofNat 64 (R14Plan.entry_c10 + c.1)))) = true := by decide

/-- **Every PC fetched by run c10 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c10) (hpath : ArmCertPipe.PathOK (extend inputs D_c10) guards_c10)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c10 regions_c10 sc base) (hp : PinsAgree p rs_c10 forms_c10 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c10.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c10 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c10 past_c10 0 entry) :
    ∀ k, k < plan_c10.length → ∃ c ∈ R14Plan.codeWords_c10,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c10 + c.1) := by
  intro k hk
  have hpc := ((run_c10 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c10 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c11 is a reviewed code word of the case. -/
theorem pcs_reviewed_c11 : (List.range plan_c11.length).all (fun k => R14Plan.codeWords_c11.any
    (fun c => decide (offset_c11 k = BitVec.ofNat 64 (R14Plan.entry_c11 + c.1)))) = true := by decide

/-- **Every PC fetched by run c11 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c11) (hpath : ArmCertPipe.PathOK (extend inputs D_c11) guards_c11)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c11.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c11 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c11 past_c11 0 entry) :
    ∀ k, k < plan_c11.length → ∃ c ∈ R14Plan.codeWords_c11,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c11 + c.1) := by
  intro k hk
  have hpc := ((run_c11 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c11 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c12 is a reviewed code word of the case. -/
theorem pcs_reviewed_c12 : (List.range plan_c12.length).all (fun k => R14Plan.codeWords_c12.any
    (fun c => decide (offset_c12 k = BitVec.ofNat 64 (R14Plan.entry_c12 + c.1)))) = true := by decide

/-- **Every PC fetched by run c12 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c12 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c12) (hpath : ArmCertPipe.PathOK (extend inputs D_c12) guards_c12)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c12 regions_c12 sc base) (hp : PinsAgree p rs_c12 forms_c12 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c12.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c12 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c12 past_c12 0 entry) :
    ∀ k, k < plan_c12.length → ∃ c ∈ R14Plan.codeWords_c12,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c12 + c.1) := by
  intro k hk
  have hpc := ((run_c12 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c12 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

/-- Static: every planned PC of case c13 is a reviewed code word of the case. -/
theorem pcs_reviewed_c13 : (List.range plan_c13.length).all (fun k => R14Plan.codeWords_c13.any
    (fun c => decide (offset_c13 k = BitVec.ofNat 64 (R14Plan.entry_c13 + c.1)))) = true := by decide

/-- **Every PC fetched by run c13 is a reviewed code word** (at load base `base`). -/
theorem fetch_covered_c13 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (sc : Nat → Prop) (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat) (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    (page : base.toNat % 4096 = 0) (low : base.toNat < 2 ^ 54) (hlen : inputs.length = n0_c13) (hpath : ArmCertPipe.PathOK (extend inputs D_c13) guards_c13)
    (ds : DataStaticR14 mapping bytePA p (rowsFootprint spec.imageRows).byte dataSites_c13 regions_c13 sc base) (hp : PinsAgree p rs_c13 forms_c13 inputs)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hroom : plan_c13.length ≤ budget)
    (entry : NativeState) (init : ReleaseProfile.DefaultRuntime.Inv_c13 spec config rows mapping table sc bytes base ifunc p budget inputs bytePA catalogue entry capacity_c13 past_c13 0 entry) :
    ∀ k, k < plan_c13.length → ∃ c ∈ R14Plan.codeWords_c13,
      (stateAt real entry k).regs._PC = base + BitVec.ofNat 64 (R14Plan.entry_c13 + c.1) := by
  intro k hk
  have hpc := ((run_c13 real spec config rows mapping table sc bytes b cb base ifunc p budget inputs bytePA cs page low hlen hpath ds hp catalogue nodup hroom entry init).1 k hk).core.v1.pc
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 pcs_reviewed_c13 k (List.mem_range.2 hk))
  exact ⟨w, hw, by rw [hpc, of_decide_eq_true he]⟩

end ReleaseProfile.DefaultRuntime

#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c00
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c01
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c02
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c03
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c04
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c05
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c06
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c07
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c08
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c09
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c10
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c11
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c12
#print axioms ReleaseProfile.DefaultRuntime.fetch_covered_c13
