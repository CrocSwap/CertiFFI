import PipeLean_D234_SecpMulAlt_c20.DitBodyRun
import DitShim243.DITFrame
import DitShim243.ControlFrame
import PipeLean_D234_SecpMulAlt_c20.DefaultABI
import TranslateSpan.FPControlFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment HeapV2StepCerts.RegBind
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMulAlt_c20.DitBodyFrames

private theorem step_2 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 2 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6652, 2600959084) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 6652 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (6652, 2600959084) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 3), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 3), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 3), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_3 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 3 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6656, 2613541997) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 6656 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (6656, 2613541997) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_4 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6660, 2601024619) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 6660 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (6660, 2601024619) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_5 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6664, 2613607534) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 6664 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (6664, 2613607534) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_6 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 6 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6668, 2869625261) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 6668 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (6668, 2869625261) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_8 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 8 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6676, 2601090155) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 6676 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (6676, 2601090155) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_9 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 9 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6680, 2613673071) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 6680 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (6680, 2613673071) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 15#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.umulh, [.reg (.x 3), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Umulh64.tailX real x 15#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 15#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.umulh, [.reg (.x 3), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Umulh64.tailX real x 15#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 15#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.umulh, [.reg (.x 3), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Umulh64.tailX real x 15#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_10 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 10 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6684, 3121283534) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 6684 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (6684, 3121283534) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_11 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 11 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6688, 2601155691) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 6688 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (6688, 2601155691) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_12 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 12 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6692, 2613738608) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 6692 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (6692, 2613738608) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 3#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 3), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 3#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 3#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 3), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 3#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 3#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 3), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 3#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_13 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 13 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6696, 3121283567) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 6696 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (6696, 3121283567) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_14 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 14 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6700, 2585723408) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 6700 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (6700, 2585723408) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 16#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 16#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 16#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_16 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 16 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6708, 2600959115) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 6708 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (6708, 2600959115) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_17 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 17 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6712, 2869625261) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 6712 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (6712, 2869625261) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_18 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 18 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6716, 2601024651) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 6716 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (6716, 2601024651) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_19 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 19 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6720, 3121283534) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 6720 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (6720, 3121283534) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_20 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 20 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6724, 2601090187) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 6724 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (6724, 2601090187) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_21 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6728, 3121283567) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 6728 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (6728, 3121283567) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_22 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6732, 2601155723) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 6732 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (6732, 2601155723) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 4#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 4), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 4#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_23 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 23 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6736, 3121283600) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 6736 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (6736, 3121283600) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_24 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 24 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6740, 2613738627) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 6740 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (6740, 2613738627) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_25 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 25 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6744, 2585722979) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 6744 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (6744, 2585722979) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_26 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 26 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6748, 2613542027) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 6748 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (6748, 2613542027) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_27 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 27 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6752, 2869625294) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 6752 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (6752, 2869625294) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 14#5 14#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.AddsShift64.tailX real x 14#5 14#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 14#5 14#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.AddsShift64.tailX real x 14#5 14#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 14#5 14#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.AddsShift64.tailX real x 14#5 14#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_28 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 28 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6756, 2613607563) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 6756 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (6756, 2613607563) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_29 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 29 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6760, 3121283567) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 6760 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (6760, 3121283567) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_30 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 30 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6764, 2613673099) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 6764 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (6764, 2613673099) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 4#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 4), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 4#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_31 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 31 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6768, 3121283600) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 6768 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (6768, 3121283600) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_32 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 32 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6772, 2585722979) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 6772 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (6772, 2585722979) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_33 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 33 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6776, 2600959147) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 6776 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (6776, 2600959147) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_34 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 34 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6780, 2869625294) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 6780 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (6780, 2869625294) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 14#5 14#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.AddsShift64.tailX real x 14#5 14#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 14#5 14#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.AddsShift64.tailX real x 14#5 14#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 14#5 14#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.AddsShift64.tailX real x 14#5 14#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_35 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 35 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6784, 2601024683) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 6784 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (6784, 2601024683) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_36 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 36 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6788, 3121283567) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 6788 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (6788, 3121283567) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_37 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 37 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6792, 2601090219) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 6792 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (6792, 2601090219) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_38 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 38 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6796, 3121283600) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 6796 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (6796, 3121283600) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_39 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 39 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6800, 2601155755) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 6800 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (6800, 2601155755) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 5), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 5#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_40 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 40 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6804, 3121283171) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 6804 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (6804, 3121283171) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_41 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 41 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6808, 2613738660) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 6808 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (6808, 2613738660) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 5), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 5#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 5), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 5#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 5), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 5#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_42 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 42 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6812, 2585723012) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 6812 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (6812, 2585723012) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_43 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 43 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6816, 2613542059) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 6816 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (6816, 2613542059) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_44 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 44 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6820, 2869625327) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 6820 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (6820, 2869625327) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_45 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 45 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6824, 2613607595) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 6824 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (6824, 2613607595) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_46 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 46 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6828, 3121283600) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 6828 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (6828, 3121283600) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_47 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 47 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6832, 2613673131) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 6832 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (6832, 2613673131) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_48 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 48 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6836, 3121283171) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 6836 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (6836, 3121283171) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_49 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 49 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6840, 2585723012) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 6840 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (6840, 2585723012) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_50 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 50 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6844, 2600959179) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_50
  have pc : x.regs._PC = MemReloc.imageAddress base 6844 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    50 x inv.core (6844, 2600959179) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_51 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 51 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6848, 2869625327) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_51
  have pc : x.regs._PC = MemReloc.imageAddress base 6848 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    51 x inv.core (6848, 2869625327) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_52 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 52 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6852, 2601024715) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 6852 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (6852, 2601024715) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_53 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 53 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6856, 3121283600) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 6856 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (6856, 3121283600) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_54 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 54 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6860, 2601090251) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 6860 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (6860, 2601090251) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_55 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 55 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6864, 3121283171) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_55
  have pc : x.regs._PC = MemReloc.imageAddress base 6864 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    55 x inv.core (6864, 3121283171) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_56 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 56 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6868, 2601155787) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 6868 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (6868, 2601155787) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 6#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 6), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 6#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_57 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 57 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6872, 3121283204) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 6872 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (6872, 3121283204) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_58 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 58 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6876, 2613738693) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 6876 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (6876, 2613738693) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 6#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 6), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 6#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 6#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 6), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 6#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 6#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 6), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 6#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_59 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 59 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6880, 2585723045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 6880 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (6880, 2585723045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_60 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 60 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6884, 2613542091) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 6884 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (6884, 2613542091) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_61 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 61 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6888, 2869625360) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 6888 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (6888, 2869625360) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 16#5 16#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.AddsShift64.tailX real x 16#5 16#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 16#5 16#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.AddsShift64.tailX real x 16#5 16#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 16#5 16#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.AddsShift64.tailX real x 16#5 16#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_62 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 62 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6892, 2613607627) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 6892 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (6892, 2613607627) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_63 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 63 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6896, 3121283171) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 6896 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (6896, 3121283171) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_64 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 64 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6900, 2613673163) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 6900 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (6900, 2613673163) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 11#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.umulh, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.Umulh64.tailX real x 11#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_65 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 65 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6904, 3121283204) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 6904 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (6904, 3121283204) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_66 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 66 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6908, 2585723045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 6908 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (6908, 2585723045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_67 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 67 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6912, 3531635239) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 6912 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (6912, 3531635239) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 7#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.Movz64z.tailX real x 7#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 7#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.Movz64z.tailX real x 7#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 7#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.Movz64z.tailX real x 7#5 977#16 (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_68 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 68 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6916, 2992636135) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 6916 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (6916, 2992636135) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_69 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 69 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6920, 2601549035) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 6920 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (6920, 2601549035) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_70 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 70 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6924, 2614131945) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 6924 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (6924, 2614131945) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 7#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 7), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 7#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 7#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 7), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 7#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 7#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 7), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 7#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_71 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 71 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6928, 2869625228) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 6928 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (6928, 2869625228) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_72 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 72 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6932, 2600697067) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 6932 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (6932, 2600697067) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_73 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 73 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6936, 2613279971) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 6936 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (6936, 2613279971) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 7#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 7), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 7#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 7#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 7), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 7#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 7#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 7), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 7#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_74 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 74 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6940, 3121283501) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 6940 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (6940, 3121283501) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_75 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 75 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6944, 2600762603) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 6944 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (6944, 2600762603) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_76 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 76 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6948, 2613345508) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_76
  have pc : x.regs._PC = MemReloc.imageAddress base 6948 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x inv.core (6948, 2613345508) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 7#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 7), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 7#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 7#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 7), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 7#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 7#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 7), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 7#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_77 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 77 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6952, 3121283534) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_77
  have pc : x.regs._PC = MemReloc.imageAddress base 6952 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x inv.core (6952, 3121283534) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_78 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 78 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6956, 2600828139) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_78
  have pc : x.regs._PC = MemReloc.imageAddress base 6956 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    78 x inv.core (6956, 2600828139) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_79 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 79 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6960, 2613411045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_79
  have pc : x.regs._PC = MemReloc.imageAddress base 6960 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    79 x inv.core (6960, 2613411045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 7), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 7), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 7), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_80 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 80 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6964, 3121283567) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_80
  have pc : x.regs._PC = MemReloc.imageAddress base 6964 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    80 x inv.core (6964, 3121283567) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_81 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 81 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6968, 2594125808) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_81
  have pc : x.regs._PC = MemReloc.imageAddress base 6968 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    81 x inv.core (6968, 2594125808) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.Csinc3.tailX real x 16#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.Csinc3.tailX real x 16#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.Csinc3.tailX real x 16#5 (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_82 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 82 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6972, 2869494189) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_82
  have pc : x.regs._PC = MemReloc.imageAddress base 6972 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    82 x inv.core (6972, 2869494189) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_83 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 83 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6976, 3120759246) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_83
  have pc : x.regs._PC = MemReloc.imageAddress base 6976 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    83 x inv.core (6976, 3120759246) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 3#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 3#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 3), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 3#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_84 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 84 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6980, 3120824815) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_84
  have pc : x.regs._PC = MemReloc.imageAddress base 6980 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    84 x inv.core (6980, 3120824815) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_85 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 85 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6984, 2584019472) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_85
  have pc : x.regs._PC = MemReloc.imageAddress base 6984 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    85 x inv.core (6984, 2584019472) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 16#5 16#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Adc64.tailX real x 16#5 16#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 16#5 16#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Adc64.tailX real x 16#5 16#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 16#5 16#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Adc64.tailX real x 16#5 16#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_86 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 86 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6988, 2432697864) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_86
  have pc : x.regs._PC = MemReloc.imageAddress base 6988 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    86 x inv.core (6988, 2432697864) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 8#5 16#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add, [.reg (.x 16), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.AddImm64.tailX real x 8#5 16#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 8#5 16#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add, [.reg (.x 16), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.AddImm64.tailX real x 8#5 16#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 8#5 16#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add, [.reg (.x 16), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.AddImm64.tailX real x 8#5 16#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_87 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 87 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6992, 2601024747) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_87
  have pc : x.regs._PC = MemReloc.imageAddress base 6992 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    87 x inv.core (6992, 2601024747) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 7#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 7), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_88 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 88 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6996, 2613607657) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_88
  have pc : x.regs._PC = MemReloc.imageAddress base 6996 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    88 x inv.core (6996, 2613607657) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 7#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 7), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 7#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 7), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 7#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 7), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_89 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 89 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7000, 2869625228) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_89
  have pc : x.regs._PC = MemReloc.imageAddress base 7000 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    89 x inv.core (7000, 2869625228) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 11#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 11), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 11#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_90 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 90 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7004, 3121152429) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_90
  have pc : x.regs._PC = MemReloc.imageAddress base 7004 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    90 x inv.core (7004, 3121152429) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_91 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 91 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7008, 3122594254) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_91
  have pc : x.regs._PC = MemReloc.imageAddress base 7008 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    91 x inv.core (7008, 3122594254) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_92 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 92 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7012, 3122594287) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_92
  have pc : x.regs._PC = MemReloc.imageAddress base 7012 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    92 x inv.core (7012, 3122594287) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 15#5 15#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 15#5 15#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 15#5 15#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_93 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 93 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7016, 2594124007) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_93
  have pc : x.regs._PC = MemReloc.imageAddress base 7016 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    93 x inv.core (7016, 2594124007) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 7), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Csel3.tailX real x 7#5 7#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 7), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Csel3.tailX real x 7#5 7#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 7), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Csel3.tailX real x 7#5 7#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_94 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 94 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7020, 3943104908) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_94
  have pc : x.regs._PC = MemReloc.imageAddress base 7020 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    94 x inv.core (7020, 3943104908) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 12#5 12#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.sbc3, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.SubsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 12#5 12#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.sbc3, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.SubsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 12#5 12#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.sbc3, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 12), .reg (.x 7), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.SubsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_95 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 95 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7024, 4196336045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_95
  have pc : x.regs._PC = MemReloc.imageAddress base 7024 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    95 x inv.core (7024, 4196336045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.sbc3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.Sbcs64.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.sbc3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.Sbcs64.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.sbc3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.Sbcs64.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_96 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 96 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7028, 4196336078) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_96
  have pc : x.regs._PC = MemReloc.imageAddress base 7028 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    96 x inv.core (7028, 4196336078) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.sbc3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 14), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Sbcs64.tailX real x 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.sbc3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 14), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Sbcs64.tailX real x 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.sbc3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 14), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 14), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Sbcs64.tailX real x 14#5 14#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_97 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 97 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7032, 3659465199) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_97
  have pc : x.regs._PC = MemReloc.imageAddress base 7032 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    97 x inv.core (7032, 3659465199) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.sbc3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (ArmCertValue.Sbc64.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.sbc3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (ArmCertValue.Sbc64.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.sbc3, [.reg (.x 15), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (ArmCertValue.Sbc64.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_0 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[0]? = some (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 1#5 0#7 = (BitVec.addInt (entryGPR initial 1) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 1)) (0) = (BitVec.addInt (entryGPR initial 1) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = X := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 1) (0)) = regionVA initial X (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 0 mapping (BitVec.addInt (entryGPR initial 1) (0)) := by
    rw [regionAddress]
    exact receipt.spans X 32 0 (by decide) (by rfl) (by decide)
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have memberCode : (6644, 2839547939) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 6644 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (6644, 2839547939) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_1 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 2#5 0#7 = (BitVec.addInt (entryGPR initial 2) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 2)) (0) = (BitVec.addInt (entryGPR initial 2) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize Y = X := by decide
  have alias := layout.aliases Y 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 2) (0)) = regionVA initial X (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, Y, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 0 mapping (BitVec.addInt (entryGPR initial 2) (0)) := by
    rw [regionAddress]
    exact receipt.spans X 32 0 (by decide) (by rfl) (by decide)
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have memberCode : (6648, 2839552071) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_1
  have codePC : x.regs._PC = MemReloc.imageAddress base 6648 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (6648, 2839552071) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 7#5 8#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 7#5 8#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 7#5 8#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_7 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 7 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_7 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 2#5 2#7 = (BitVec.addInt (entryGPR initial 2) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 2)) (16) = (BitVec.addInt (entryGPR initial 2) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize Y = X := by decide
  have alias := layout.aliases Y 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 2) (16)) = regionVA initial X (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, Y, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 2 mapping (BitVec.addInt (entryGPR initial 2) (16)) := by
    rw [regionAddress]
    exact receipt.spans X 32 2 (by decide) (by rfl) (by decide)
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_7 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 7 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (7+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 7 + 4#64 = offset EntryBinding.plan (7+1) from by decide)
  have memberCode : (6672, 2839619657) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_7
  have codePC : x.regs._PC = MemReloc.imageAddress base 6672 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (6672, 2839619657) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_7 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 9#5 10#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_7] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_7 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 9#5 10#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_7] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_7 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 9#5 10#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_7] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_15 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 15 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_15 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 1#5 2#7 = (BitVec.addInt (entryGPR initial 1) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 1)) (16) = (BitVec.addInt (entryGPR initial 1) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = X := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 1) (16)) = regionVA initial X (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 2 mapping (BitVec.addInt (entryGPR initial 1) (16)) := by
    rw [regionAddress]
    exact receipt.spans X 32 2 (by decide) (by rfl) (by decide)
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_15 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 15 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (15+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 15 + 4#64 = offset EntryBinding.plan (15+1) from by decide)
  have memberCode : (6704, 2839615525) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_15
  have codePC : x.regs._PC = MemReloc.imageAddress base 6704 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (6704, 2839615525) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_15 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_15] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_15 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_15] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_15 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_15] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_98 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 98 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[4]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_98 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 0#5 0#7 = (BitVec.addInt (entryGPR initial 0) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 0)) (0) = (BitVec.addInt (entryGPR initial 0) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize O = O := by decide
  have alias := layout.aliases O 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 0) (0)) = regionVA initial O (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, O, O, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) O 0 mapping (BitVec.addInt (entryGPR initial 0) (0)) := by
    rw [regionAddress]
    exact receipt.spans O 32 0 (by decide) (by rfl) (by decide)
  have targets := SelectedStoreFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) member)
  have output := SecpCurrentEntry.output_safe (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) EntryBinding.plan raw mapping base initial rfl layout
    O 32 0 (by decide) (by decide)
  have facts := DefaultSelectedPairFacts.store_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (rowsFootprint raw.imageRows).byte (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) O 0
    0#7 0#5 x source span targets output
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 98 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (98+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 98 + 4#64 = offset EntryBinding.plan (98+1) from by decide)
  have memberCode : (7036, 2835362828) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_98
  have codePC : x.regs._PC = MemReloc.imageAddress base 7036 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    98 x inv.core (7036, 2835362828) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_98 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 12#5 13#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 12#5 13#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_98] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_98 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 12#5 13#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 12#5 13#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_98] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_98 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 12#5 13#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 12#5 13#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_98] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_99 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 99 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[5]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_99 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 0#5 2#7 = (BitVec.addInt (entryGPR initial 0) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 0)) (16) = (BitVec.addInt (entryGPR initial 0) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize O = O := by decide
  have alias := layout.aliases O 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 0) (16)) = regionVA initial O (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, O, O, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) O 2 mapping (BitVec.addInt (entryGPR initial 0) (16)) := by
    rw [regionAddress]
    exact receipt.spans O 32 2 (by decide) (by rfl) (by decide)
  have targets := SelectedStoreFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) member)
  have output := SecpCurrentEntry.output_safe (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) EntryBinding.plan raw mapping base initial rfl layout
    O 32 2 (by decide) (by decide)
  have facts := DefaultSelectedPairFacts.store_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (rowsFootprint raw.imageRows).byte (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial)
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) O 2
    2#7 0#5 x source span targets output
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 99 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (99+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 99 + 4#64 = offset EntryBinding.plan (99+1) from by decide)
  have memberCode : (7040, 2835430414) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_99
  have codePC : x.regs._PC = MemReloc.imageAddress base 7040 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    99 x inv.core (7040, 2835430414) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_99 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 14#5 15#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 14#5 15#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_99] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_99 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 14#5 15#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 14#5 15#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_99] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_99 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 14#5 15#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 14#5 15#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_99] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_100 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 100 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have low := receipt.low
  have original := DefaultTerminal.original_lr mapping initial x inv.agrees
  have currentLow : (x.regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [original]; exact low
  have member : (7044, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[100]? = some (7044, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7044 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    100 x inv.core (7044, 0xd65f03c0) member pc
  have fp := FPControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have dit := DitShim243.DITFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have ctl := DitShim243.ControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  exact ⟨fp,dit,ctl⟩

private theorem all_steps (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (k : Nat) (bound : k < 101)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x)
    (actual : modelStep real x = .ok () fin) : (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have selected : k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100] : List Nat) := by
    change k ∈ List.range 101
    exact List.mem_range.mpr bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100
  · subst k; exact step_0 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_1 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_2 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_3 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_4 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_5 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_6 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_7 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_8 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_9 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_10 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_11 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_12 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_13 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_14 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_15 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_16 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_17 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_18 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_19 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_20 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_21 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_22 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_23 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_24 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_25 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_26 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_27 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_28 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_29 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_30 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_31 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_32 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_33 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_34 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_35 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_36 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_37 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_38 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_39 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_40 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_41 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_42 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_43 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_44 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_45 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_46 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_47 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_48 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_49 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_50 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_51 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_52 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_53 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_54 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_55 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_56 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_57 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_58 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_59 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_60 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_61 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_62 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_63 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_64 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_65 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_66 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_67 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_68 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_69 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_70 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_71 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_72 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_73 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_74 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_75 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_76 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_77 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_78 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_79 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_80 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_81 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_82 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_83 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_84 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_85 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_86 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_87 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_88 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_89 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_90 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_91 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_92 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_93 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_94 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_95 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_96 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_97 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_98 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_99 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_100 real raw config rows mapping base initial topology layout page receipt x fin inv actual

theorem preserves (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 101 →
      ((stateAt real initial k).regs.FPCR = initial.regs.FPCR ∧
       (stateAt real initial k).regs.FPSR = initial.regs.FPSR) ∧
      (stateAt real initial k).regs.PSTATE.DIT = initial.regs.PSTATE.DIT ∧
      RtPremC.ctlv (stateAt real initial k).regs = RtPremC.ctlv initial.regs := by
  obtain ⟨_,steps,invariants,-⟩ := DitBodyRun.run real raw config rows mapping base initial topology receipt
  intro k
  induction k with
  | zero => intro _; exact ⟨⟨rfl,rfl⟩,rfl,rfl⟩
  | succ j ih =>
    intro bound
    have prior := ih (by omega)
    have current := all_steps real raw config rows mapping base initial topology receipt.layout receipt.page receipt
      j (by omega) (stateAt real initial j) (stateAt real initial (j+1))
      (invariants j (by omega)) (steps j (by omega))
    exact ⟨⟨current.1.1.trans prior.1.1,current.1.2.trans prior.1.2⟩,
      current.2.1.trans prior.2.1,current.2.2.trans prior.2.2⟩

#print axioms preserves
end PipeLean_D234_SecpMulAlt_c20.DitBodyFrames
