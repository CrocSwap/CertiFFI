import PipeLean_D234_SecpSqr_c24.DitBodyRun
import DitShim243.DITFrame
import DitShim243.ControlFrame
import PipeLean_D234_SecpSqr_c24.DefaultABI
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
namespace PipeLean_D234_SecpSqr_c24.DitBodyFrames

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
  have member : (7056, 2611641666) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 7056 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (7056, 2611641666) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 2#5 10#5 10#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 2#5 10#5 10#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 2#5 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 2#5 10#5 10#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 2#5 10#5 10#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 2#5 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 2#5 10#5 10#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 2#5 10#5 10#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 2#5 10#5 10#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7060, 3546348878) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 7060 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (7060, 3546348878) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7064, 2611903939) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 7064 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (7064, 2611903939) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 3#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 3#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 3#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 3#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 3#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 3#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 3#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 3#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 3#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7068, 2611903822) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 7068 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (7068, 2611903822) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 10#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 10#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 10#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 10#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 10#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 10#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 10#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 10#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 10#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7072, 2869855298) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 7072 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (7072, 2869855298) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 2#5 2#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 2#5 2#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 2#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 2#5 2#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 2#5 2#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 2#5 2#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 2#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 2#5 2#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 2#5 2#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 2#5 2#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 2#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 2#5 2#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7076, 3546283470) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 7076 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (7076, 3546283470) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7080, 2584608867) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 7080 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (7080, 2584608867) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 3#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Adc64.tailX real x 3#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 3#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Adc64.tailX real x 3#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 3#5 3#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.Adc64.tailX real x 3#5 3#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7084, 2611707236) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 7084 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (7084, 2611707236) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 4#5 11#5 11#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 4#5 11#5 11#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 4#5 11#5 11#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 4#5 11#5 11#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 4#5 11#5 11#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 4#5 11#5 11#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 4#5 11#5 11#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 4#5 11#5 11#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 4#5 11#5 11#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7088, 3546348910) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 7088 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (7088, 3546348910) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7092, 2611903941) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 7092 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (7092, 2611903941) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7096, 2611903854) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 7096 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (7096, 2611903854) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 11#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 11#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 11#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 11#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 11#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 11#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 11#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 11#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 11#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7100, 2601221455) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 7100 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (7100, 2601221455) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7104, 2613804368) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 7104 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (7104, 2613804368) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7108, 2869855364) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 7108 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (7108, 2869855364) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7112, 3546283470) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 7112 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (7112, 3546283470) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7116, 2584608933) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 7116 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (7116, 2584608933) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 5#5 5#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Adc64.tailX real x 5#5 5#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 5#5 5#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Adc64.tailX real x 5#5 5#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 5#5 5#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Adc64.tailX real x 5#5 5#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7120, 2869887471) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 7120 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (7120, 2869887471) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7124, 3121611280) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 7124 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (7124, 3121611280) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7128, 2585723045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 7128 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (7128, 2585723045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7132, 2869887075) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 7132 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (7132, 2869887075) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7136, 3121610884) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 7136 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (7136, 3121610884) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7140, 2585723045) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 7140 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (7140, 2585723045) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7144, 2611772806) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 7144 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (7144, 2611772806) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 6#5 12#5 12#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 6#5 12#5 12#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 6#5 12#5 12#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 6#5 12#5 12#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 6#5 12#5 12#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 6#5 12#5 12#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 6#5 12#5 12#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 6#5 12#5 12#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 6#5 12#5 12#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7148, 3546348942) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_25
  have pc : x.regs._PC = MemReloc.imageAddress base 7148 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (7148, 3546348942) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 25
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_25] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7152, 2611903943) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_26
  have pc : x.regs._PC = MemReloc.imageAddress base 7152 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (7152, 2611903943) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 7#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 7#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 7#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 7#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 7#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 7#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 26
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 7#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 7#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_26] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 7#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7156, 2611903886) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 7156 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (7156, 2611903886) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 12#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 12#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 12#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 12#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 12#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 12#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 12#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 12#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 12#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7160, 2869855430) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 7160 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (7160, 2869855430) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 6#5 6#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 6#5 6#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 6#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 6#5 6#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 6#5 6#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 6#5 6#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 6#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 6#5 6#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 6#5 6#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 6#5 6#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 6#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 6#5 6#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7164, 3546283470) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 7164 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (7164, 3546283470) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7168, 2584608999) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 7168 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (7168, 2584608999) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 7#5 7#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Adc64.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 7#5 7#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Adc64.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 7#5 7#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Adc64.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7172, 2611838376) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 7172 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (7172, 2611838376) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 8#5 13#5 13#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 8#5 13#5 13#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 8#5 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 8#5 13#5 13#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 8#5 13#5 13#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 8#5 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 8#5 13#5 13#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 8#5 13#5 13#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 8#5 13#5 13#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7176, 3546348974) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 7176 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (7176, 3546348974) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 13#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 13#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 14#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 32), [.reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 14#5 13#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7180, 2611903945) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 7180 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (7180, 2611903945) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 9#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 9#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 9#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 9#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 9#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 9#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 9#5 14#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 9#5 14#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 9#5 14#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7184, 2611903918) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 7184 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (7184, 2611903918) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 13#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 13#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 13#5 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 13#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 13#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 13#5 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 13#5 14#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 13#5 14#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 13#5 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7188, 2601352591) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 7188 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (7188, 2601352591) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 12#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 12), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 12#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 12), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 12#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 12), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7192, 2613935504) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 7192 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (7192, 2613935504) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 12#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 12), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 12#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 12), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 12#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 12), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7196, 2869855496) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 7196 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (7196, 2869855496) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 8#5 8#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 8#5 8#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 8#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 8#5 8#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 8#5 8#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 8#5 8#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 8#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 8#5 8#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 8#5 8#5 33#6 14#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 8#5 8#5 33#6 14#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 8#5 33#6 14#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 8#5 8#5 33#6 14#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7200, 3546283470) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 7200 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (7200, 3546283470) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨(.lsr 31), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7204, 2584609065) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 7204 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (7204, 2584609065) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7208, 2869887471) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 7208 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (7208, 2869887471) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7212, 3121611280) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 7212 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (7212, 3121611280) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7216, 2585723177) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 7216 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (7216, 2585723177) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7220, 2869887207) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 7220 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (7220, 2869887207) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7224, 3121611016) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 7224 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (7224, 3121611016) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7228, 2585723177) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 7228 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (7228, 2585723177) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7232, 3943432522) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 7232 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (7232, 3943432522) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 12), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7236, 4195156331) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 7236 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (7236, 4195156331) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 11#5 11#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 11#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 11#5 11#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 11#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 11#5 11#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 11), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 11), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 11#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7240, 3667862512) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 7240 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (7240, 3667862512) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (7244, 3390046538) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 7244 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (7244, 3390046538) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 10#5 10#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.eor, [.reg (.x 10), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.SecpEor64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 10#5 10#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.eor, [.reg (.x 10), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.SecpEor64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 10#5 10#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.eor, [.reg (.x 10), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.SecpEor64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7248, 3943694666) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_50
  have pc : x.regs._PC = MemReloc.imageAddress base 7248 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    50 x inv.core (7248, 3943694666) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 50
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 10#5 10#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 10), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_50] using ob)
    (ArmCertValue.SubsShift64.tailX real x 10#5 10#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7252, 3390046571) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_51
  have pc : x.regs._PC = MemReloc.imageAddress base 7252 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    51 x inv.core (7252, 3390046571) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 11#5 11#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.eor, [.reg (.x 11), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.SecpEor64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 11#5 11#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.eor, [.reg (.x 11), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.SecpEor64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 51
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 11#5 11#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.eor, [.reg (.x 11), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_51] using ob)
    (ArmCertValue.SecpEor64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7256, 3658482027) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 7256 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (7256, 3658482027) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 11#5 11#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 11#5 11#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 11#5 11#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.sbc3, [.reg (.x 11), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 11#5 11#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7260, 2869166278) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 7260 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (7260, 2869166278) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 6#5 6#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.AddsShift64.tailX real x 6#5 6#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 6#5 6#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.AddsShift64.tailX real x 6#5 6#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 6#5 6#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.AddsShift64.tailX real x 6#5 6#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7264, 3120890087) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 7264 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (7264, 3120890087) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 5), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 5#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7268, 3122594056) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_55
  have pc : x.regs._PC = MemReloc.imageAddress base 7268 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    55 x inv.core (7268, 3122594056) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 8#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 8#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 55
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 8#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_55] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7272, 2585723177) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 7272 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (7272, 2585723177) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7276, 2611641676) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 7276 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (7276, 2611641676) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 12#5 10#5 10#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 12#5 10#5 10#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 12#5 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 12#5 10#5 10#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 12#5 10#5 10#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 12#5 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 12#5 10#5 10#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 12#5 10#5 10#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 12#5 10#5 10#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7280, 3546348869) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 7280 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (7280, 3546348869) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 5#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 5#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 10)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 5#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7284, 2611313837) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 7284 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (7284, 2611313837) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 13#5 5#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 13#5 5#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 13#5 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 13#5 5#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 13#5 5#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 13#5 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 13#5 5#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 13#5 5#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 13#5 5#5 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7288, 2611313989) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 7288 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (7288, 2611313989) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 10#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 10#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 10#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 10#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 10#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 10#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 10#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 10#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 10#5 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7292, 2869265804) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 7292 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (7292, 2869265804) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 33#6 5#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 33#6 5#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 33#6 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 33#6 5#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 33#6 5#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 33#6 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 33#6 5#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 33#6 5#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 33#6 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7296, 3546283173) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 7296 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (7296, 3546283173) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7300, 2584019373) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 7300 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (7300, 2584019373) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 13#5 13#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adc64.tailX real x 13#5 13#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 13#5 13#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adc64.tailX real x 13#5 13#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 13#5 13#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.Adc64.tailX real x 13#5 13#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7304, 2611707247) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 7304 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (7304, 2611707247) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 15#5 11#5 11#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 15#5 11#5 11#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 15#5 11#5 11#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 15#5 11#5 11#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 15#5 11#5 11#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 15#5 11#5 11#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 15#5 11#5 11#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 15#5 11#5 11#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 15#5 11#5 11#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7308, 3546348901) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 7308 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (7308, 3546348901) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 5#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 5#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 5#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 32), [.reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 5#5 11#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7312, 2611313838) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 7312 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (7312, 2611313838) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 5#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 5#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 5#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 5#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 14#5 5#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 14#5 5#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 14#5 5#5 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7316, 2611314021) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 7316 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (7316, 2611314021) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 11#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 11#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 11#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 11#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 11#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 11#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (N1D226.Umaddl64Generic.Encoding.selected 5#5 11#5 5#5) _ (x.regs._PC + 4#64)
    (N1D226.Umaddl64Generic.DriverValue.upd x 5#5 11#5 5#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (N1D226.Umaddl64Generic.DriverValue.tailX real x 5#5 11#5 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7320, 2601221444) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 7320 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (7320, 2601221444) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7324, 2613804368) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 7324 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (7324, 2613804368) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 16#5 10#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.umulh, [.reg (.x 10), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Umulh64.tailX real x 16#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7328, 2869265903) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 7328 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (7328, 2869265903) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 15#5 15#5 33#6 5#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 15#5 15#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 15#5 33#6 5#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 15#5 15#5 33#6 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 15#5 15#5 33#6 5#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 15#5 15#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 15#5 33#6 5#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 15#5 15#5 33#6 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 15#5 15#5 33#6 5#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 15#5 15#5 33#6 5#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 15#5 33#6 5#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 15#5 15#5 33#6 5#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7332, 3546283173) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 7332 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (7332, 3546283173) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr31.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨(.lsr 31), [.reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.SecpLsr31.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7336, 2584019406) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 7336 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (7336, 2584019406) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 5), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7340, 2869166212) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 7340 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (7340, 2869166212) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 4#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 4#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7344, 3121611280) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 7344 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (7344, 3121611280) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.add3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 16), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Adcs64.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7348, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 7348 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (7348, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7352, 2869166509) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_76
  have pc : x.regs._PC = MemReloc.imageAddress base 7352 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x inv.core (7352, 2869166509) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 4#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 4), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7356, 3121611247) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_77
  have pc : x.regs._PC = MemReloc.imageAddress base 7356 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x inv.core (7356, 3121611247) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7360, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_78
  have pc : x.regs._PC = MemReloc.imageAddress base 7360 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    78 x inv.core (7360, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7364, 2869297220) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_79
  have pc : x.regs._PC = MemReloc.imageAddress base 7364 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    79 x inv.core (7364, 2869297220) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 2#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 2#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 2#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 2#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 4#5 2#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 6), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.AddsShift64.tailX real x 4#5 2#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7368, 3121021029) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_80
  have pc : x.regs._PC = MemReloc.imageAddress base 7368 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    80 x inv.core (7368, 3121021029) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 3#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 7), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 3#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7372, 3121086662) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_81
  have pc : x.regs._PC = MemReloc.imageAddress base 7372 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    81 x inv.core (7372, 3121086662) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 6#5 6#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.Adcs64.tailX real x 6#5 6#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7376, 3121152231) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_82
  have pc : x.regs._PC = MemReloc.imageAddress base 7376 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    82 x inv.core (7376, 3121152231) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 7#5 7#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (ArmCertValue.Adcs64.tailX real x 7#5 7#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7380, 3667862512) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_83
  have pc : x.regs._PC = MemReloc.imageAddress base 7380 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    83 x inv.core (7380, 3667862512) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (7384, 3943432324) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_84
  have pc : x.regs._PC = MemReloc.imageAddress base 7384 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    84 x inv.core (7384, 3943432324) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 12), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7388, 4195156133) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_85
  have pc : x.regs._PC = MemReloc.imageAddress base 7388 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    85 x inv.core (7388, 4195156133) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 5#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 5#5 5#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 5#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 5#5 5#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 5#5 5#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 13), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 5#5 5#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7392, 4195287238) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_86
  have pc : x.regs._PC = MemReloc.imageAddress base 7392 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    86 x inv.core (7392, 4195287238) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7396, 4195221735) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_87
  have pc : x.regs._PC = MemReloc.imageAddress base 7396 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    87 x inv.core (7396, 4195221735) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 7#5 7#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 7#5 7#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 7#5 7#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 14), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 7#5 7#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7400, 3121611016) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_88
  have pc : x.regs._PC = MemReloc.imageAddress base 7400 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    88 x inv.core (7400, 3121611016) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7404, 2584740137) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_89
  have pc : x.regs._PC = MemReloc.imageAddress base 7404 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    89 x inv.core (7404, 2584740137) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 9#5 9#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (ArmCertValue.Adc64.tailX real x 9#5 9#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7408, 3531635249) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_90
  have pc : x.regs._PC = MemReloc.imageAddress base 7408 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    90 x inv.core (7408, 3531635249) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 17#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.Movz64z.tailX real x 17#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 17#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.Movz64z.tailX real x 17#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 17#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.Movz64z.tailX real x 17#5 977#16 (by decide) (by decide) ⟨⟩) actual
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
  have member : (7412, 2992636464) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_91
  have pc : x.regs._PC = MemReloc.imageAddress base 7412 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    91 x inv.core (7412, 2992636464) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 16#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.orr, [.reg (.x 17), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 16#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 16#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.orr, [.reg (.x 17), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 16#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 16#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.orr, [.reg (.x 17), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 16#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7416, 2600893962) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_92
  have pc : x.regs._PC = MemReloc.imageAddress base 7416 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    92 x inv.core (7416, 2600893962) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 10#5 16#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 16), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.Madd64.tailX real x 10#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 10#5 16#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 16), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.Madd64.tailX real x 10#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 10#5 16#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 16), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.Madd64.tailX real x 10#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7420, 2613476877) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_93
  have pc : x.regs._PC = MemReloc.imageAddress base 7420 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    93 x inv.core (7420, 2613476877) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 16#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 16), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 16#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 16), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 16#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 16), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 16#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7424, 2453699814) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_94
  have pc : x.regs._PC = MemReloc.imageAddress base 7424 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    94 x inv.core (7424, 2453699814) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 7), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 7), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 7), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7428, 3546348775) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_95
  have pc : x.regs._PC = MemReloc.imageAddress base 7428 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    95 x inv.core (7428, 3546348775) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 7#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 7)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 7#5 7#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7432, 2600893995) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_96
  have pc : x.regs._PC = MemReloc.imageAddress base 7432 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    96 x inv.core (7432, 2600893995) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7436, 2600933926) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_97
  have pc : x.regs._PC = MemReloc.imageAddress base 7436 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    97 x inv.core (7436, 2600933926) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (7440, 2869330283) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_98
  have pc : x.regs._PC = MemReloc.imageAddress base 7440 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    98 x inv.core (7440, 2869330283) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 98
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 11#5 11#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 11#5 11#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 11#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_98] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 11#5 11#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 98
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 11#5 11#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 11#5 11#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 11#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_98] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 11#5 11#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 98
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 11#5 11#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 11#5 11#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 11#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_98] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 11#5 11#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
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
  have member : (7444, 3546348742) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_99
  have pc : x.regs._PC = MemReloc.imageAddress base 7444 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    99 x inv.core (7444, 3546348742) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 99
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_99] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 99
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_99] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 99
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_99] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (7448, 2584084718) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_100
  have pc : x.regs._PC = MemReloc.imageAddress base 7448 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    100 x inv.core (7448, 2584084718) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 7#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_100] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 7#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_100] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 7#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_100] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_101 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 101 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7452, 2601025036) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_101
  have pc : x.regs._PC = MemReloc.imageAddress base 7452 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    101 x inv.core (7452, 2601025036) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 101
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_101] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 101
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_101] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 101
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_101] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_102 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 102 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7456, 2613607944) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_102
  have pc : x.regs._PC = MemReloc.imageAddress base 7456 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    102 x inv.core (7456, 2613607944) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 102
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 16#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 16), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_102] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 102
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 16#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 16), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_102] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 102
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 16#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 16), .reg (.x 8)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_102] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 16#5 8#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_103 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 103 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7460, 2453699878) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_103
  have pc : x.regs._PC = MemReloc.imageAddress base 7460 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    103 x inv.core (7460, 2453699878) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 103
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 9), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_103] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 103
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 9), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_103] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 103
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.and, [.reg (.x 9), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_103] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 6#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_104 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 104 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7464, 3546348839) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_104
  have pc : x.regs._PC = MemReloc.imageAddress base 7464 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    104 x inv.core (7464, 3546348839) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 104
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_104] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 7#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 104
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_104] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 7#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 104
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 7#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨(.lsr 32), [.reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_104] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 7#5 9#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_105 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 105 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7468, 2600893993) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_105
  have pc : x.regs._PC = MemReloc.imageAddress base 7468 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    105 x inv.core (7468, 2600893993) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 105
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_105] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 105
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_105] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 105
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_105] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_106 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 106 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7472, 2600933926) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_106
  have pc : x.regs._PC = MemReloc.imageAddress base 7472 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    106 x inv.core (7472, 2600933926) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 106
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_106] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 106
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_106] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 106
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 6#5 17#5 6#5 7#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 6#5 17#5 6#5 7#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_106] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 6#5 17#5 6#5 7#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_107 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 107 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7476, 2869330217) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_107
  have pc : x.regs._PC = MemReloc.imageAddress base 7476 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    107 x inv.core (7476, 2869330217) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 107
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 9#5 9#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 9#5 9#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 9#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_107] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 9#5 9#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 107
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 9#5 9#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 9#5 9#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 9#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_107] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 9#5 9#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 107
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 9#5 9#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 9#5 9#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 9#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_107] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 9#5 9#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_108 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 108 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7480, 3546348742) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_108
  have pc : x.regs._PC = MemReloc.imageAddress base 7480 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    108 x inv.core (7480, 3546348742) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 108
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_108] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 108
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_108] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 108
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 6#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_108] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 6#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_109 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 109 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7484, 2584084719) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_109
  have pc : x.regs._PC = MemReloc.imageAddress base 7484 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    109 x inv.core (7484, 2584084719) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 109
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 15#5 7#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_109] using ob)
    (ArmCertValue.Adc64.tailX real x 15#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 109
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 15#5 7#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_109] using ob)
    (ArmCertValue.Adc64.tailX real x 15#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 109
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 15#5 7#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 7), .reg (.x 6), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_109] using ob)
    (ArmCertValue.Adc64.tailX real x 15#5 7#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_110 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 110 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7488, 2869559362) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_110
  have pc : x.regs._PC = MemReloc.imageAddress base 7488 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    110 x inv.core (7488, 2869559362) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 110
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_110] using ob)
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 110
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_110] using ob)
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 110
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_110] using ob)
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_111 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 111 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7492, 3121283171) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_111
  have pc : x.regs._PC = MemReloc.imageAddress base 7492 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    111 x inv.core (7492, 3121283171) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 111
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_111] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 111
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_111] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 111
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_111] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_112 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 112 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7496, 3121348740) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_112
  have pc : x.regs._PC = MemReloc.imageAddress base 7496 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    112 x inv.core (7496, 3121348740) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 112
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_112] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 112
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_112] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 112
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_112] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_113 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 113 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7500, 3121152165) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_113
  have pc : x.regs._PC = MemReloc.imageAddress base 7500 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    113 x inv.core (7500, 3121152165) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 113
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_113] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 113
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_113] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 113
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_113] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_114 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 114 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7504, 2594125798) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_114
  have pc : x.regs._PC = MemReloc.imageAddress base 7504 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    114 x inv.core (7504, 2594125798) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 114
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_114] using ob)
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 114
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_114] using ob)
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 114
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_114] using ob)
    (ArmCertValue.Csinc3.tailX real x 6#5 (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_115 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 115 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7508, 2869756003) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_115
  have pc : x.regs._PC = MemReloc.imageAddress base 7508 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    115 x inv.core (7508, 2869756003) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 115
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 13#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_115] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 115
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 13#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_115] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 115
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 3#5 3#5 0#6 13#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_115] using ob)
    (ArmCertValue.AddsShift64.tailX real x 3#5 3#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_116 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 116 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7512, 3121479812) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_116
  have pc : x.regs._PC = MemReloc.imageAddress base 7512 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    116 x inv.core (7512, 3121479812) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 116
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_116] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 116
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_116] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 116
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 4#5 4#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_116] using ob)
    (ArmCertValue.Adcs64.tailX real x 4#5 4#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_117 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 117 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7516, 3121086629) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_117
  have pc : x.regs._PC = MemReloc.imageAddress base 7516 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    117 x inv.core (7516, 3121086629) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 117
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_117] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 117
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_117] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 117
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 5#5 5#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_117] using ob)
    (ArmCertValue.Adcs64.tailX real x 5#5 5#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_118 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 118 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7520, 2584674502) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_118
  have pc : x.regs._PC = MemReloc.imageAddress base 7520 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    118 x inv.core (7520, 2584674502) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 118
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_118] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 118
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_118] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 118
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_118] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_119 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 119 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7524, 2432697542) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_119
  have pc : x.regs._PC = MemReloc.imageAddress base 7524 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    119 x inv.core (7524, 2432697542) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 119
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 6#5 6#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add, [.reg (.x 6), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_119] using ob)
    (ArmCertValue.AddImm64.tailX real x 6#5 6#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 119
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 6#5 6#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add, [.reg (.x 6), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_119] using ob)
    (ArmCertValue.AddImm64.tailX real x 6#5 6#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 119
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 6#5 6#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add, [.reg (.x 6), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_119] using ob)
    (ArmCertValue.AddImm64.tailX real x 6#5 6#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_120 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 120 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7528, 2600893994) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_120
  have pc : x.regs._PC = MemReloc.imageAddress base 7528 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    120 x inv.core (7528, 2600893994) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 120
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 10#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_120] using ob)
    (ArmCertValue.Madd64.tailX real x 10#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 120
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 10#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_120] using ob)
    (ArmCertValue.Madd64.tailX real x 10#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 120
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 10#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.mul, [.reg (.x 17), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_120] using ob)
    (ArmCertValue.Madd64.tailX real x 10#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_121 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 121 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7532, 3546348747) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_121
  have pc : x.regs._PC = MemReloc.imageAddress base 7532 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    121 x inv.core (7532, 3546348747) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 121
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 11#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_121] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 11#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 121
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 11#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_121] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 11#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 121
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 11#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨(.lsr 32), [.reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_121] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 11#5 6#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_122 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 122 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7536, 2869330250) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_122
  have pc : x.regs._PC = MemReloc.imageAddress base 7536 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    122 x inv.core (7536, 2869330250) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 122
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 10#5 10#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 10#5 10#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 10#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_122] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 10#5 10#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 122
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 10#5 10#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 10#5 10#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 10#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_122] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 10#5 10#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 122
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 10#5 10#5 32#6 6#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 10#5 10#5 32#6 6#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 10#5 32#6 6#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_122] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 10#5 10#5 32#6 6#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_123 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 123 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7540, 2584413163) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_123
  have pc : x.regs._PC = MemReloc.imageAddress base 7540 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    123 x inv.core (7540, 2584413163) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 123
    (by decide) page (by decide) (N1D226.AdcZeroRn64Generic.Encoding.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.lit 0#64, .reg (.x 11), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_123] using ob)
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 11#5 11#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 123
    (by decide) page (by decide) (N1D226.AdcZeroRn64Generic.Encoding.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.lit 0#64, .reg (.x 11), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_123] using ob)
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 11#5 11#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 123
    (by decide) page (by decide) (N1D226.AdcZeroRn64Generic.Encoding.selected 11#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.lit 0#64, .reg (.x 11), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_123] using ob)
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 11#5 11#5 (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_124 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 124 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7544, 2869559362) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_124
  have pc : x.regs._PC = MemReloc.imageAddress base 7544 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    124 x inv.core (7544, 2869559362) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 124
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_124] using ob)
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 124
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_124] using ob)
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 124
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 2#5 2#5 0#6 10#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.add3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 10), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_124] using ob)
    (ArmCertValue.AddsShift64.tailX real x 2#5 2#5 0#6 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_125 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 125 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7548, 3121283171) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_125
  have pc : x.regs._PC = MemReloc.imageAddress base 7548 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    125 x inv.core (7548, 3121283171) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 125
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_125] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 125
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_125] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 125
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 3#5 3#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.add3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_125] using ob)
    (ArmCertValue.Adcs64.tailX real x 3#5 3#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_126 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 126 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7552, 3122593924) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_126
  have pc : x.regs._PC = MemReloc.imageAddress base 7552 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    126 x inv.core (7552, 3122593924) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 126
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_126] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 126
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_126] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 126
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_126] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_127 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 127 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7556, 3122593957) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_127
  have pc : x.regs._PC = MemReloc.imageAddress base 7556 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    127 x inv.core (7556, 3122593957) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 127
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_127] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 127
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_127] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 127
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.add3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_127] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 5#5 5#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_128 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 128 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7560, 2594124304) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_128
  have pc : x.regs._PC = MemReloc.imageAddress base 7560 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    128 x inv.core (7560, 2594124304) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 128
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 16), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_128] using ob)
    (ArmCertValue.Csel3.tailX real x 16#5 16#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 128
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 16), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_128] using ob)
    (ArmCertValue.Csel3.tailX real x 16#5 16#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 128
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 16#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 16), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_128] using ob)
    (ArmCertValue.Csel3.tailX real x 16#5 16#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_129 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 129 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7564, 3943694402) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_129
  have pc : x.regs._PC = MemReloc.imageAddress base 7564 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    129 x inv.core (7564, 3943694402) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 129
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 2#5 2#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.sbc3, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_129] using ob)
    (ArmCertValue.SubsShift64.tailX real x 2#5 2#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 129
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 2#5 2#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.sbc3, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_129] using ob)
    (ArmCertValue.SubsShift64.tailX real x 2#5 2#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 129
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 2#5 2#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.sbc3, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 2), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_129] using ob)
    (ArmCertValue.SubsShift64.tailX real x 2#5 2#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_130 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 130 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7568, 4196335715) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_130
  have pc : x.regs._PC = MemReloc.imageAddress base 7568 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    130 x inv.core (7568, 4196335715) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 130
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 3), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_130] using ob)
    (ArmCertValue.Sbcs64.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 130
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 3), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_130] using ob)
    (ArmCertValue.Sbcs64.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 130
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 3#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 3), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 3), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_130] using ob)
    (ArmCertValue.Sbcs64.tailX real x 3#5 3#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_131 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 131 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7572, 4196335748) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_131
  have pc : x.regs._PC = MemReloc.imageAddress base 7572 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    131 x inv.core (7572, 4196335748) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 131
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_131] using ob)
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 131
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_131] using ob)
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 131
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_131] using ob)
    (ArmCertValue.Sbcs64.tailX real x 4#5 4#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_132 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 132 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (7576, 3659464869) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_132
  have pc : x.regs._PC = MemReloc.imageAddress base 7576 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    132 x inv.core (7576, 3659464869) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 132
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_132] using ob)
    (ArmCertValue.Sbc64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 132
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_132] using ob)
    (ArmCertValue.Sbc64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 132
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 5#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_132] using ob)
    (ArmCertValue.Sbc64.tailX real x 5#5 5#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have memberCode : (7048, 2839555114) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 7048 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (7048, 2839555114) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 10#5 11#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 10#5 11#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_0] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_0 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 10#5 11#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 10#5 11#5 0#7 1#5 g sp mm nz pay)
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
  have memberCode : (7052, 2839622700) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_1
  have codePC : x.regs._PC = MemReloc.imageAddress base 7052 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (7052, 2839622700) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 12#5 13#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 12#5 13#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 12#5 13#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 12#5 13#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_133 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 133 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_133 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 133 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (133+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 133 + 4#64 = offset EntryBinding.plan (133+1) from by decide)
  have memberCode : (7580, 2835352578) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_133
  have codePC : x.regs._PC = MemReloc.imageAddress base 7580 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    133 x inv.core (7580, 2835352578) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_133 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 2#5 3#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_133] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_133 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 2#5 3#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_133] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_133 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 2#5 3#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 2#5 3#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_133] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_134 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 134 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_134 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 134 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (134+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 134 + 4#64 = offset EntryBinding.plan (134+1) from by decide)
  have memberCode : (7584, 2835420164) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_134
  have codePC : x.regs._PC = MemReloc.imageAddress base 7584 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    134 x inv.core (7584, 2835420164) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_134 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 4#5 5#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_134] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_134 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 4#5 5#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_134] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_134 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 4#5 5#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 4#5 5#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_134] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_135 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 135 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have low := receipt.low
  have original := DefaultTerminal.original_lr mapping initial x inv.agrees
  have currentLow : (x.regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [original]; exact low
  have member : (7588, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[135]? = some (7588, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7588 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    135 x inv.core (7588, 0xd65f03c0) member pc
  have fp := FPControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 135
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have dit := DitShim243.DITFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 135
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have ctl := DitShim243.ControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 135
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
    (k : Nat) (bound : k < 136)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x)
    (actual : modelStep real x = .ok () fin) : (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have selected : k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135] : List Nat) := by
    change k ∈ List.range 136
    exact List.mem_range.mpr bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127 | h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135
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
  · subst k; exact step_101 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_102 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_103 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_104 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_105 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_106 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_107 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_108 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_109 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_110 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_111 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_112 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_113 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_114 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_115 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_116 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_117 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_118 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_119 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_120 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_121 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_122 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_123 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_124 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_125 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_126 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_127 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_128 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_129 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_130 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_131 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_132 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_133 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_134 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_135 real raw config rows mapping base initial topology layout page receipt x fin inv actual

theorem preserves (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 136 →
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
end PipeLean_D234_SecpSqr_c24.DitBodyFrames
