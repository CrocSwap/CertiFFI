import PipeLean_D234_SecpMod4_c30.DitBodyRun
import DitShim243.DITFrame
import DitShim243.ControlFrame
import PipeLean_D234_SecpMod4_c30.DefaultABI
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
namespace PipeLean_D234_SecpMod4_c30.DitBodyFrames

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
  have member : (8040, 2315518054) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 8040 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (8040, 2315518054) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAnd64.selected 6#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.SecpAnd64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAnd64.selected 6#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.SecpAnd64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAnd64.selected 6#5 3#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 3), .reg (.x 4)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.SecpAnd64.tailX real x 6#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (8044, 2315583686) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 8044 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (8044, 2315583686) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAnd64.selected 6#5 6#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 6), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.SecpAnd64.tailX real x 6#5 6#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAnd64.selected 6#5 6#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 6), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.SecpAnd64.tailX real x 6#5 6#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAnd64.selected 6#5 6#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 6), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.SecpAnd64.tailX real x 6#5 6#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (8048, 3531635239) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 8048 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (8048, 3531635239) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 7#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Movz64z.tailX real x 7#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 7#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Movz64z.tailX real x 7#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 7#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Movz64z.tailX real x 7#5 977#16 (by decide) (by decide) ⟨⟩) actual
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
  have member : (8052, 2992636135) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 8052 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (8052, 2992636135) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.orr, [.reg (.x 7), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (8056, 2869035239) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 8056 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (8056, 2869035239) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 2#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 2#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 2#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 2), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 2#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (8060, 3122593990) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 8060 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (8060, 3122593990) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 6#5 6#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8064, 2592550978) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 8064 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (8064, 2592550978) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 2#5 2#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 2), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 2#5 2#5 7#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 2#5 2#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 2), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 2#5 2#5 7#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 2#5 2#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 2), .reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 2#5 2#5 7#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8068, 2592485475) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 8068 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (8068, 2592485475) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 3#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 3#5 3#5 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 3#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 3#5 3#5 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 3#5 3#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 3), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 3#5 3#5 6#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8072, 2592485508) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 8072 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (8072, 2592485508) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 4#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 4#5 4#5 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 4#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 4#5 4#5 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 4#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 4#5 4#5 6#5 (by decide) (by decide) (by decide)) actual
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
  have member : (8076, 2592485541) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 8076 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (8076, 2592485541) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 5#5 5#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 5), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 5#5 5#5 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 5#5 5#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 5), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 5#5 5#5 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (N1D226.CselCc64Generic.Encoding.selected 5#5 5#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 5), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (N1D226.CselCc64Generic.Value.tailX real x 5#5 5#5 6#5 (by decide) (by decide) (by decide)) actual
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
  have memberCode : (8032, 2839546914) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 8032 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (8032, 2839546914) memberCode codePC
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
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[1]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_1 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 1 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have memberCode : (8036, 2839614500) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_1
  have codePC : x.regs._PC = MemReloc.imageAddress base 8036 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (8036, 2839614500) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 4#5 5#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 4#5 5#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 4#5 5#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 4#5 5#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_12 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 12 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (12+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 12 + 4#64 = offset EntryBinding.plan (12+1) from by decide)
  have memberCode : (8080, 2835352578) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_12
  have codePC : x.regs._PC = MemReloc.imageAddress base 8080 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (8080, 2835352578) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_12 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 2#5 3#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_12] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_12 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 2#5 3#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_12] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_12 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 2#5 3#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_12] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_13 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 13 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (13+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 13 + 4#64 = offset EntryBinding.plan (13+1) from by decide)
  have memberCode : (8084, 2835420164) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_13
  have codePC : x.regs._PC = MemReloc.imageAddress base 8084 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (8084, 2835420164) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_13 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 4#5 5#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_13] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_13 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 4#5 5#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_13] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_13 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 4#5 5#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_13] using ob) fin actual
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
  have low := receipt.low
  have original := DefaultTerminal.original_lr mapping initial x inv.agrees
  have currentLow : (x.regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [original]; exact low
  have member : (8088, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[14]? = some (8088, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 8088 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (8088, 0xd65f03c0) member pc
  have fp := FPControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have dit := DitShim243.DITFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have ctl := DitShim243.ControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
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
    (k : Nat) (bound : k < 15)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x)
    (actual : modelStep real x = .ok () fin) : (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have selected : k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] : List Nat) := by
    change k ∈ List.range 15
    exact List.mem_range.mpr bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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

theorem preserves (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 15 →
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
end PipeLean_D234_SecpMod4_c30.DitBodyFrames
