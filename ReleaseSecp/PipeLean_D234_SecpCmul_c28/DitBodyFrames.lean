import PipeLean_D234_SecpCmul_c28.DitBodyRun
import DitShim243.DITFrame
import DitShim243.ControlFrame
import PipeLean_D234_SecpCmul_c28.DefaultABI
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
namespace PipeLean_D234_SecpCmul_c28.DitBodyFrames

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
  have member : (7916, 2600959011) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 7916 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (7916, 2600959011) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7920, 2601024548) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 7920 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (7920, 2601024548) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 1#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 1), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 1#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 1), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 1#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 1), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7924, 2601090085) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 7924 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (7924, 2601090085) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 5#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 1), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 5#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 5#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 1), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 5#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 5#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 1), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 5#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7928, 2601155622) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 7928 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (7928, 2601155622) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 6#5 1#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.mul, [.reg (.x 1), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Madd64.tailX real x 6#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 6#5 1#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.mul, [.reg (.x 1), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Madd64.tailX real x 6#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 6#5 1#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.mul, [.reg (.x 1), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Madd64.tailX real x 6#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7932, 2613541927) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 7932 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (7932, 2613541927) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 1#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 1), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 1#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 1), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 7#5 1#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.umulh, [.reg (.x 1), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.Umulh64.tailX real x 7#5 1#5 7#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7936, 2613607464) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 7936 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (7936, 2613607464) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 1#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 1), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 1#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 1), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 1#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 1), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 1#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7940, 2613673001) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 7940 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (7940, 2613673001) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 1), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 1), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 9#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.umulh, [.reg (.x 1), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Umulh64.tailX real x 9#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7944, 2613738538) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 7944 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (7944, 2613738538) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 1#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 1), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 1#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 1), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 1#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 1), .reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 1#5 10#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7948, 2869362820) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 7948 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (7948, 2869362820) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7952, 3121086629) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 7952 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (7952, 3121086629) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7956, 3121152198) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 7956 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (7956, 3121152198) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7960, 3122594122) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 7960 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (7960, 3122594122) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7964, 2432697674) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 7964 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (7964, 2432697674) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 10#5 10#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add, [.reg (.x 10), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.AddImm64.tailX real x 10#5 10#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 10#5 10#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add, [.reg (.x 10), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.AddImm64.tailX real x 10#5 10#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 10#5 10#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add, [.reg (.x 10), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.AddImm64.tailX real x 10#5 10#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
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
  have member : (7968, 3531635241) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 7968 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (7968, 3531635241) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 9#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Movz64z.tailX real x 9#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 9#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Movz64z.tailX real x 9#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 9#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Movz64z.tailX real x 9#5 977#16 (by decide) (by decide) ⟨⟩) actual
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
  have member : (7972, 2992636201) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 7972 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (7972, 2992636201) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.orr, [.reg (.x 9), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.orr, [.reg (.x 9), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.orr, [.reg (.x 9), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7976, 2601090375) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 7976 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (7976, 2601090375) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 10#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 10), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 10#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 10), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 10#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 10), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7980, 2613673288) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 7980 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (7980, 2613673288) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 10#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 10), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 10#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 10), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 10#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 10), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 10#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7984, 2869362787) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 7984 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (7984, 2869362787) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7988, 3121086596) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 7988 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (7988, 3121086596) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7992, 3122593957) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 7992 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (7992, 3122593957) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7996, 3122593990) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 7996 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (7996, 3122593990) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8000, 2594124073) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 8000 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (8000, 2594124073) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 9), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Csel3.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 9), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Csel3.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 9), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Csel3.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8004, 3943235683) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 8004 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (8004, 3943235683) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 9), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (8008, 4196335748) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 8008 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (8008, 4196335748) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8012, 4196335781) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 8012 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (8012, 4196335781) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Sbcs64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Sbcs64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (ArmCertValue.Sbcs64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8016, 3659464902) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 8016 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (8016, 3659464902) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Sbc64.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Sbc64.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Sbc64.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[0]? = some (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 2#5 0#7 = (BitVec.addInt (entryGPR initial 2) (0)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 2)) (0) = (BitVec.addInt (entryGPR initial 2) (0))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = X := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 0)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 2) (0)) = regionVA initial X (8 * 0) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 0 mapping (BitVec.addInt (entryGPR initial 2) (0)) := by
    rw [regionAddress]
    exact receipt.spans X 32 0 (by decide) (by rfl) (by decide)
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_0 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 0 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have memberCode : (7908, 2839552071) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 7908 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (7908, 2839552071) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 7#5 8#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 7#5 8#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 7#5 8#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 7#5 8#5 0#7 2#5 g sp mm nz pay)
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
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  rw [input] at pointer
  have source : LdpBytes.pairAddr x 2#5 2#7 = (BitVec.addInt (entryGPR initial 2) (16)) := by
    change BitVec.addInt (HeapV2StepCerts.RegBind.regVal x (.x 2)) (16) = (BitVec.addInt (entryGPR initial 2) (16))
    rw [pointer]
  have normalized : EntryBinding.plan.normalize X = X := by decide
  have alias := layout.aliases X 32 (by decide)
  rw [normalized] at alias
  have shifted := congrArg (fun a => PageSplit.byteVA a (8 * 2)) alias
  have regionAddress : (BitVec.addInt (entryGPR initial 2) (16)) = regionVA initial X (8 * 2) := by
    simpa [SecpCurrentEntry.regionVA_add, regionVA, X, X, BitVec.addInt, PageSplit.byteVA] using shifted
  have span : SelectedBinding.At (view EntryBinding.plan mapping initial) X 2 mapping (BitVec.addInt (entryGPR initial 2) (16)) := by
    rw [regionAddress]
    exact receipt.spans X 32 2 (by decide) (by rfl) (by decide)
  have targets := SelectedLoadFacts.targets_of_check (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (rowsFootprint raw.imageRows).byte
    (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base) (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (beforeFetchState initial) initialInv.core.closed (rams (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member)
  obtain ⟨data,payload⟩ := PairData.load_payload_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have memberCode : (7912, 2839619657) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_1
  have codePC : x.regs._PC = MemReloc.imageAddress base 7912 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (7912, 2839619657) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 9#5 10#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 9#5 10#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 9#5 10#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_28 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 28 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (28+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 28 + 4#64 = offset EntryBinding.plan (28+1) from by decide)
  have memberCode : (8020, 2835353603) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_28
  have codePC : x.regs._PC = MemReloc.imageAddress base 8020 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (8020, 2835353603) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_28 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 3#5 4#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 3#5 4#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_28] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_28 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 3#5 4#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 3#5 4#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_28] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_28 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 3#5 4#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 3#5 4#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_28] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_29 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 29 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (29+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 29 + 4#64 = offset EntryBinding.plan (29+1) from by decide)
  have memberCode : (8024, 2835421189) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_29
  have codePC : x.regs._PC = MemReloc.imageAddress base 8024 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (8024, 2835421189) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_29 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 5#5 6#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_29] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_29 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 5#5 6#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_29] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_29 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 5#5 6#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 5#5 6#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_29] using ob) fin actual
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
  have low := receipt.low
  have original := DefaultTerminal.original_lr mapping initial x inv.agrees
  have currentLow : (x.regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [original]; exact low
  have member : (8028, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[30]? = some (8028, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 8028 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (8028, 0xd65f03c0) member pc
  have fp := FPControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have dit := DitShim243.DITFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have ctl := DitShim243.ControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
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
    (k : Nat) (bound : k < 31)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x)
    (actual : modelStep real x = .ok () fin) : (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have selected : k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30] : List Nat) := by
    change k ∈ List.range 31
    exact List.mem_range.mpr bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30
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

theorem preserves (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 31 →
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
end PipeLean_D234_SecpCmul_c28.DitBodyFrames
