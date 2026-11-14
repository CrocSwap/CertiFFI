import PipeLean_D234_SecpSqrAlt_c26.DitBodyRun
import DitShim243.DITFrame
import DitShim243.ControlFrame
import PipeLean_D234_SecpSqrAlt_c26.DefaultABI
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
namespace PipeLean_D234_SecpSqrAlt_c26.DitBodyFrames

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
  have member : (7596, 2600696905) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_1
  have pc : x.regs._PC = MemReloc.imageAddress base 7596 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (7596, 2600696905) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 1
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 2#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 2), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_1] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 1
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 2#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 2), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_1] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 1
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 2#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 2), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_1] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

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
  have member : (7600, 2613279818) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 7600 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (7600, 2613279818) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 2#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 2), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 2#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 2), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 2#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 2), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7608, 2600827979) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 7608 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (7608, 2600827979) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 2#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 2), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 2#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 2), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 2#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 2), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7612, 2613410892) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 7612 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (7612, 2613410892) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 12#5 2#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 2), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 12#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 12#5 2#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 2), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 12#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 12#5 2#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 2), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 12#5 2#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7616, 2600762439) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 7616 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (7616, 2600762439) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 2#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 2), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 2#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 2), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 2#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 2), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7620, 2613345350) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 7620 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (7620, 2613345350) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 2#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 2), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 2#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 2), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 2#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 2), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 2#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7624, 2869363018) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 7624 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (7624, 2869363018) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 10#5 10#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.AddsShift64.tailX real x 10#5 10#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 10#5 10#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.AddsShift64.tailX real x 10#5 10#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 10#5 10#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.AddsShift64.tailX real x 10#5 10#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7628, 3120955755) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 7628 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (7628, 3120955755) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7632, 2600762471) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 7632 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (7632, 2600762471) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7636, 2613345382) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 7636 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (7636, 2613345382) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7640, 2585723078) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 7640 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (7640, 2585723078) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7644, 2869363051) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 7644 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (7644, 2869363051) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7648, 2600828045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 7648 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (7648, 2600828045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7652, 2613410958) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 7652 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (7652, 2613410958) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7656, 3120955788) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 7656 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (7656, 3120955788) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7660, 2600828007) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 7660 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (7660, 2600828007) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7664, 2613410918) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 7664 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (7664, 2613410918) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7668, 2585723078) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 7668 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (7668, 2585723078) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7672, 2869363084) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 7672 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (7672, 2869363084) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 12#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 12#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7676, 3120955821) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 7676 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (7676, 3120955821) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7680, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 7680 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (7680, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7684, 2869494057) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 7684 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (7684, 2869494057) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7688, 3121217866) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 7688 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (7688, 3121217866) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7692, 3121283435) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 7692 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (7692, 3121283435) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7696, 3121349004) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 7696 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (7696, 3121349004) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7700, 3121414573) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 7700 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (7700, 3121414573) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7704, 3121480142) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 7704 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (7704, 3121480142) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7708, 2594125798) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 7708 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (7708, 2594125798) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) actual
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
  have member : (7712, 2613214279) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 7712 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (7712, 2613214279) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 2#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 2), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 2#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 2), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 2#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 2), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7716, 2600631368) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 7716 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (7716, 2600631368) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 8#5 2#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.mul, [.reg (.x 2), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.Madd64.tailX real x 8#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 8#5 2#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.mul, [.reg (.x 2), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.Madd64.tailX real x 8#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 8#5 2#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.mul, [.reg (.x 2), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.Madd64.tailX real x 8#5 2#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7720, 2869362985) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 7720 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (7720, 2869362985) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7724, 2600696935) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 7724 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (7724, 2600696935) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7728, 3121021258) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 7728 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (7728, 3121021258) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7732, 2613279847) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 7732 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (7732, 2613279847) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 3), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 3), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 3), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 3#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7736, 3121021291) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 7736 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (7736, 3121021291) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7740, 2600762503) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 7740 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (7740, 2600762503) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 4), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 4), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 4), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7744, 3121021324) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 7744 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (7744, 3121021324) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7748, 2613345415) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 7748 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (7748, 2613345415) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 4), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 4), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 4), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 4#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7752, 3121021357) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 7752 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (7752, 3121021357) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7756, 2600828071) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 7756 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (7756, 2600828071) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 5), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 5), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 5), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7760, 3121021390) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 7760 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (7760, 3121021390) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 14#5 14#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adcs64.tailX real x 14#5 14#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7764, 2613410983) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 7764 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (7764, 2613410983) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 5), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 5), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 5), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 5#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7768, 2584150214) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 7768 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (7768, 2584150214) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 7), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 7), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 7), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7772, 3531635235) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 7772 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (7772, 3531635235) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 3#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Movz64z.tailX real x 3#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 3#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Movz64z.tailX real x 3#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 3#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Movz64z.tailX real x 3#5 977#16 (by decide) (by decide) ⟨⟩) actual
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
  have member : (7776, 2992636003) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 7776 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (7776, 2992636003) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.orr, [.reg (.x 3), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.orr, [.reg (.x 3), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.orr, [.reg (.x 3), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 3#5 3#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7780, 2601286759) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 7780 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (7780, 2601286759) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7784, 2613869668) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 7784 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (7784, 2613869668) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 3#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 3), .reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 3#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 3), .reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 4#5 3#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.umulh, [.reg (.x 3), .reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Umulh64.tailX real x 4#5 3#5 12#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7788, 2869362952) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 7788 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (7788, 2869362952) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7792, 2601352295) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_50
  have pc : x.regs._PC = MemReloc.imageAddress base 7792 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    50 x inv.core (7792, 2601352295) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7796, 2613935213) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_51
  have pc : x.regs._PC = MemReloc.imageAddress base 7796 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    51 x inv.core (7796, 2613935213) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 3), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7800, 3121021225) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 7800 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (7800, 3121021225) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7804, 2601417831) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 7804 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (7804, 2601417831) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7808, 2614000750) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 7808 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (7808, 2614000750) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 3), .reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7812, 3121021258) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_55
  have pc : x.regs._PC = MemReloc.imageAddress base 7812 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    55 x inv.core (7812, 3121021258) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7816, 2600893543) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 7816 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (7816, 2600893543) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7820, 2613476454) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 7820 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (7820, 2613476454) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7824, 3121021291) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 7824 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (7824, 3121021291) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7828, 2594125804) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 7828 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (7828, 2594125804) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.Csinc3.tailX real x 12#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.Csinc3.tailX real x 12#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.Csinc3.tailX real x 12#5 (by decide) (by decide)) actual
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
  have member : (7832, 2869166377) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 7832 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (7832, 2869166377) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7836, 3121414474) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 7836 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (7836, 3121414474) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7840, 3121480043) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 7840 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (7840, 3121480043) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 11#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7844, 2584084876) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 7844 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (7844, 2584084876) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 12#5 12#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adc64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 12#5 12#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adc64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 12#5 12#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adc64.tailX real x 12#5 12#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7848, 2432697730) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 7848 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (7848, 2432697730) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 2#5 12#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add, [.reg (.x 12), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.AddImm64.tailX real x 2#5 12#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 2#5 12#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add, [.reg (.x 12), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.AddImm64.tailX real x 2#5 12#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 2#5 12#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add, [.reg (.x 12), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.AddImm64.tailX real x 2#5 12#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
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
  have member : (7852, 2600631399) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 7852 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (7852, 2600631399) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7856, 2613214310) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 7856 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (7856, 2613214310) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 3#5 2#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 3), .reg (.x 2)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 3#5 2#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7860, 2869362952) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 7860 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (7860, 2869362952) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7864, 3120955689) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 7864 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (7864, 3120955689) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7868, 3122594122) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 7868 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (7868, 3122594122) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7872, 3122594155) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 7872 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (7872, 3122594155) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 11#5 11#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 11#5 11#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 11), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 11#5 11#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7876, 2594123875) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 7876 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (7876, 2594123875) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.Csel3.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.Csel3.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.Csel3.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7880, 3942842632) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 7880 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (7880, 3942842632) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 8#5 8#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.SubsShift64.tailX real x 8#5 8#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 8#5 8#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.SubsShift64.tailX real x 8#5 8#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 8#5 8#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 8), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.SubsShift64.tailX real x 8#5 8#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7884, 4196335913) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 7884 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (7884, 4196335913) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7888, 4196335946) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 7888 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (7888, 4196335946) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Sbcs64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Sbcs64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Sbcs64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7892, 3659465067) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 7892 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (7892, 3659465067) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Sbc64.tailX real x 11#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Sbc64.tailX real x 11#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Sbc64.tailX real x 11#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have memberCode : (7592, 2839546914) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 7592 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (7592, 2839546914) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 2#5 3#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 2#5 3#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 2#5 3#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 2#5 3#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_3 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_3 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 3 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (3+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 3 + 4#64 = offset EntryBinding.plan (3+1) from by decide)
  have memberCode : (7604, 2839614500) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_3
  have codePC : x.regs._PC = MemReloc.imageAddress base 7604 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (7604, 2839614500) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_3 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 4#5 5#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_3] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_3 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 4#5 5#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_3] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_3 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 4#5 5#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_3] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_76 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 76 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (76+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 76 + 4#64 = offset EntryBinding.plan (76+1) from by decide)
  have memberCode : (7896, 2835358728) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_76
  have codePC : x.regs._PC = MemReloc.imageAddress base 7896 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x inv.core (7896, 2835358728) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_76 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 8#5 9#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 8#5 9#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_76] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_76 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 8#5 9#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 8#5 9#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_76] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_76 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 8#5 9#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 8#5 9#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_76] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_77 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 77 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (77+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 77 + 4#64 = offset EntryBinding.plan (77+1) from by decide)
  have memberCode : (7900, 2835426314) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_77
  have codePC : x.regs._PC = MemReloc.imageAddress base 7900 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x inv.core (7900, 2835426314) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_77 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 10#5 11#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 10#5 11#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_77] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_77 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 10#5 11#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 10#5 11#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_77] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_77 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 10#5 11#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 10#5 11#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_77] using ob) fin actual
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
  have low := receipt.low
  have original := DefaultTerminal.original_lr mapping initial x inv.agrees
  have currentLow : (x.regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [original]; exact low
  have member : (7904, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[78]? = some (7904, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7904 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    78 x inv.core (7904, 0xd65f03c0) member pc
  have fp := FPControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have dit := DitShim243.DITFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have ctl := DitShim243.ControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
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
    (k : Nat) (bound : k < 79)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x)
    (actual : modelStep real x = .ok () fin) : (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have selected : k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78] : List Nat) := by
    change k ∈ List.range 79
    exact List.mem_range.mpr bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78
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

theorem preserves (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 79 →
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
end PipeLean_D234_SecpSqrAlt_c26.DitBodyFrames
