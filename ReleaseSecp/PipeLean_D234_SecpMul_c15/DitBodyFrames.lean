import PipeLean_D234_SecpMul_c15.DitBodyRun
import DitShim243.DITFrame
import DitShim243.ControlFrame
import PipeLean_D234_SecpMul_c15.DefaultABI
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
namespace PipeLean_D234_SecpMul_c15.DitBodyFrames

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
  have member : (6020, 2600828007) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_2
  have pc : x.regs._PC = MemReloc.imageAddress base 6020 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    2 x inv.core (6020, 2600828007) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 2
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 7#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_2] using ob)
    (ArmCertValue.Madd64.tailX real x 7#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6024, 2613410920) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_3
  have pc : x.regs._PC = MemReloc.imageAddress base 6024 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x inv.core (6024, 2613410920) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 3
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 8#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_3] using ob)
    (ArmCertValue.Umulh64.tailX real x 8#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6028, 2600893577) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_4
  have pc : x.regs._PC = MemReloc.imageAddress base 6028 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x inv.core (6028, 2600893577) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 4
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 9#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_4] using ob)
    (ArmCertValue.Madd64.tailX real x 9#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6032, 2613476490) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_5
  have pc : x.regs._PC = MemReloc.imageAddress base 6032 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x inv.core (6032, 2613476490) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 5
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 10#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_5] using ob)
    (ArmCertValue.Umulh64.tailX real x 10#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6036, 3942842500) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_6
  have pc : x.regs._PC = MemReloc.imageAddress base 6036 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    6 x inv.core (6036, 3942842500) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 6
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_6] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6040, 3666093188) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_7
  have pc : x.regs._PC = MemReloc.imageAddress base 6040 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x inv.core (6040, 3666093188) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 7
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_7] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6044, 3667862512) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_8
  have pc : x.regs._PC = MemReloc.imageAddress base 6044 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    8 x inv.core (6044, 3667862512) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 8
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_8] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (6048, 2869428521) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_9
  have pc : x.regs._PC = MemReloc.imageAddress base 6048 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    9 x inv.core (6048, 2869428521) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 8#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 8#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 9
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 9#5 0#6 8#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 8), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_9] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 9#5 0#6 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6052, 2585723210) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_10
  have pc : x.regs._PC = MemReloc.imageAddress base 6052 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    10 x inv.core (6052, 2585723210) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 10
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_10] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6056, 3943039139) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_11
  have pc : x.regs._PC = MemReloc.imageAddress base 6056 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    11 x inv.core (6056, 3943039139) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 11
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_11] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6060, 3666027619) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_12
  have pc : x.regs._PC = MemReloc.imageAddress base 6060 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    12 x inv.core (6060, 3666027619) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 12
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_12] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6064, 3666878992) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_13
  have pc : x.regs._PC = MemReloc.imageAddress base 6064 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    13 x inv.core (6064, 3666878992) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 13
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_13] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6068, 2600696975) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_14
  have pc : x.regs._PC = MemReloc.imageAddress base 6068 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    14 x inv.core (6068, 2600696975) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 14
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_14] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6072, 2613279875) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_15
  have pc : x.regs._PC = MemReloc.imageAddress base 6072 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x inv.core (6072, 2613279875) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 15
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_15] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6076, 2869493992) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_16
  have pc : x.regs._PC = MemReloc.imageAddress base 6076 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x inv.core (6076, 2869493992) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 7#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 7#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 7#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 7#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 16
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 7#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_16] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 7#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6080, 3121217833) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_17
  have pc : x.regs._PC = MemReloc.imageAddress base 6080 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    17 x inv.core (6080, 3121217833) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 17
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_17] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6084, 2585723210) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_18
  have pc : x.regs._PC = MemReloc.imageAddress base 6084 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    18 x inv.core (6084, 2585723210) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 18
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_18] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6088, 2969568799) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_19
  have pc : x.regs._PC = MemReloc.imageAddress base 6088 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    19 x inv.core (6088, 2969568799) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 19
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_19] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
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
  have member : (6092, 3390046703) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_20
  have pc : x.regs._PC = MemReloc.imageAddress base 6092 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    20 x inv.core (6092, 3390046703) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 20
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_20] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6096, 3121086952) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_21
  have pc : x.regs._PC = MemReloc.imageAddress base 6096 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    21 x inv.core (6096, 3121086952) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 15#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 15#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 15#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 15#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 21
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 15#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_21] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 15#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6100, 3390046307) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_22
  have pc : x.regs._PC = MemReloc.imageAddress base 6100 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    22 x inv.core (6100, 3390046307) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 22
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_22] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6104, 3121152105) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_23
  have pc : x.regs._PC = MemReloc.imageAddress base 6104 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    23 x inv.core (6104, 3121152105) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 23
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 3#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_23] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 3#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6108, 2584740170) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_24
  have pc : x.regs._PC = MemReloc.imageAddress base 6108 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    24 x inv.core (6108, 2584740170) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 10#5 10#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Adc64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 10#5 10#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Adc64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 24
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 10#5 10#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_24] using ob)
    (ArmCertValue.Adc64.tailX real x 10#5 10#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6120, 2600828011) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_27
  have pc : x.regs._PC = MemReloc.imageAddress base 6120 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    27 x inv.core (6120, 2600828011) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 27
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_27] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6124, 2613410924) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_28
  have pc : x.regs._PC = MemReloc.imageAddress base 6124 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    28 x inv.core (6124, 2613410924) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 12#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Umulh64.tailX real x 12#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 12#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Umulh64.tailX real x 12#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 28
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 12#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_28] using ob)
    (ArmCertValue.Umulh64.tailX real x 12#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6128, 2600893581) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_29
  have pc : x.regs._PC = MemReloc.imageAddress base 6128 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    29 x inv.core (6128, 2600893581) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 29
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 13#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_29] using ob)
    (ArmCertValue.Madd64.tailX real x 13#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6132, 2613476494) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_30
  have pc : x.regs._PC = MemReloc.imageAddress base 6132 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    30 x inv.core (6132, 2613476494) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 30
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 14#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_30] using ob)
    (ArmCertValue.Umulh64.tailX real x 14#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6136, 3942842500) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_31
  have pc : x.regs._PC = MemReloc.imageAddress base 6136 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    31 x inv.core (6136, 3942842500) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 31
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_31] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6140, 3666093188) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_32
  have pc : x.regs._PC = MemReloc.imageAddress base 6140 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    32 x inv.core (6140, 3666093188) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 32
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_32] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6144, 3667862512) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_33
  have pc : x.regs._PC = MemReloc.imageAddress base 6144 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    33 x inv.core (6144, 3667862512) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 33
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_33] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (6148, 2869690797) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_34
  have pc : x.regs._PC = MemReloc.imageAddress base 6148 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    34 x inv.core (6148, 2869690797) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 34
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 13#5 13#5 0#6 12#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 12), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_34] using ob)
    (ArmCertValue.AddsShift64.tailX real x 13#5 13#5 0#6 12#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6152, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_35
  have pc : x.regs._PC = MemReloc.imageAddress base 6152 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    35 x inv.core (6152, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 35
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_35] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6156, 3943039139) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_36
  have pc : x.regs._PC = MemReloc.imageAddress base 6156 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    36 x inv.core (6156, 3943039139) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 36
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_36] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6160, 3666027619) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_37
  have pc : x.regs._PC = MemReloc.imageAddress base 6160 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    37 x inv.core (6160, 3666027619) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 37
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 3#5 3#5 3#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 3#5 3#5 3#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_37] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 3#5 3#5 3#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6164, 3666878992) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_38
  have pc : x.regs._PC = MemReloc.imageAddress base 6164 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    38 x inv.core (6164, 3666878992) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 38
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 16#5 16#5 16#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 16#5 16#5 16#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_38] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 16#5 16#5 16#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6168, 2600696975) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_39
  have pc : x.regs._PC = MemReloc.imageAddress base 6168 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    39 x inv.core (6168, 2600696975) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 39
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_39] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6172, 2613279875) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_40
  have pc : x.regs._PC = MemReloc.imageAddress base 6172 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    40 x inv.core (6172, 2613279875) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 40
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 3#5 4#5 3#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.umulh, [.reg (.x 4), .reg (.x 3)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_40] using ob)
    (ArmCertValue.Umulh64.tailX real x 3#5 4#5 3#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6176, 2869756268) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_41
  have pc : x.regs._PC = MemReloc.imageAddress base 6176 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    41 x inv.core (6176, 2869756268) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 11#5 0#6 13#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 11#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 11#5 0#6 13#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 11#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 41
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 12#5 11#5 0#6 13#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 13), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_41] using ob)
    (ArmCertValue.AddsShift64.tailX real x 12#5 11#5 0#6 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6180, 3121480109) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_42
  have pc : x.regs._PC = MemReloc.imageAddress base 6180 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    42 x inv.core (6180, 3121480109) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 42
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 14), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_42] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 14#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6184, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_43
  have pc : x.regs._PC = MemReloc.imageAddress base 6184 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    43 x inv.core (6184, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 43
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_43] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6188, 2969568799) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_44
  have pc : x.regs._PC = MemReloc.imageAddress base 6188 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    44 x inv.core (6188, 2969568799) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 44
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_44] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
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
  have member : (6192, 3390046703) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_45
  have pc : x.regs._PC = MemReloc.imageAddress base 6192 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    45 x inv.core (6192, 3390046703) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 45
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_45] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6196, 3121349100) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_46
  have pc : x.regs._PC = MemReloc.imageAddress base 6196 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    46 x inv.core (6196, 3121349100) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 15#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 15#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 15#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 15#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 46
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 15#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_46] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 15#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6200, 3390046307) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_47
  have pc : x.regs._PC = MemReloc.imageAddress base 6200 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    47 x inv.core (6200, 3390046307) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 47
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_47] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6204, 3121414253) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_48
  have pc : x.regs._PC = MemReloc.imageAddress base 6204 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    48 x inv.core (6204, 3121414253) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 48
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 3#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 3), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_48] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 3#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6208, 2584740302) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_49
  have pc : x.regs._PC = MemReloc.imageAddress base 6208 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    49 x inv.core (6208, 2584740302) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 49
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_49] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6220, 3943628899) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_52
  have pc : x.regs._PC = MemReloc.imageAddress base 6220 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    52 x inv.core (6220, 3943628899) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 52
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 15), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_52] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6224, 4195352708) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_53
  have pc : x.regs._PC = MemReloc.imageAddress base 6224 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    53 x inv.core (6224, 4195352708) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 53
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 16), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_53] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6228, 3667862512) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_54
  have pc : x.regs._PC = MemReloc.imageAddress base 6228 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    54 x inv.core (6228, 3667862512) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 54
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_54] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 16#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (6236, 3942973925) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_56
  have pc : x.regs._PC = MemReloc.imageAddress base 6236 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    56 x inv.core (6236, 3942973925) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 5#5 15#5 0#6 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.SubsShift64.tailX real x 5#5 15#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 5#5 15#5 0#6 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.SubsShift64.tailX real x 5#5 15#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 56
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 5#5 15#5 0#6 5#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 15), .reg (.x 5), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_56] using ob)
    (ArmCertValue.SubsShift64.tailX real x 5#5 15#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6240, 4194697766) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_57
  have pc : x.regs._PC = MemReloc.imageAddress base 6240 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    57 x inv.core (6240, 4194697766) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 57
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64Reg.selected 6#5 17#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3C, [.reg (.x 17), .reg (.x 6), .flag 2]⟩, ⟨.sbc3V, [.reg (.x 17), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_57] using ob)
    (ArmCertValue.Sbcs64Reg.tailX real x 6#5 17#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6244, 3667862513) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_58
  have pc : x.regs._PC = MemReloc.imageAddress base 6244 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    58 x inv.core (6244, 3667862513) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 17#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 17#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 17#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 17#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 58
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 17#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_58] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 17#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (6248, 3390046307) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_59
  have pc : x.regs._PC = MemReloc.imageAddress base 6248 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    59 x inv.core (6248, 3390046307) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 59
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 3#5 3#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.eor, [.reg (.x 3), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_59] using ob)
    (ArmCertValue.SecpEor64.tailX real x 3#5 3#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6252, 3943694435) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_60
  have pc : x.regs._PC = MemReloc.imageAddress base 6252 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    60 x inv.core (6252, 3943694435) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 60
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 3#5 3#5 0#6 16#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.sbc3, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 3), .reg (.x 16), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_60] using ob)
    (ArmCertValue.SubsShift64.tailX real x 3#5 3#5 0#6 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6256, 3390046340) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_61
  have pc : x.regs._PC = MemReloc.imageAddress base 6256 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    61 x inv.core (6256, 3390046340) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.eor, [.reg (.x 4), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.SecpEor64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.eor, [.reg (.x 4), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.SecpEor64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 61
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.eor, [.reg (.x 4), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_61] using ob)
    (ArmCertValue.SecpEor64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6260, 3658481796) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_62
  have pc : x.regs._PC = MemReloc.imageAddress base 6260 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    62 x inv.core (6260, 3658481796) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 62
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 4#5 4#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_62] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 4#5 4#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6264, 3390111909) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_63
  have pc : x.regs._PC = MemReloc.imageAddress base 6264 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    63 x inv.core (6264, 3390111909) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 63
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_63] using ob)
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6268, 3943760037) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_64
  have pc : x.regs._PC = MemReloc.imageAddress base 6268 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    64 x inv.core (6268, 3943760037) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 5#5 5#5 0#6 17#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.SubsShift64.tailX real x 5#5 5#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 5#5 5#5 0#6 17#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.SubsShift64.tailX real x 5#5 5#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 64
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 5#5 5#5 0#6 17#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.sbc3, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 17), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_64] using ob)
    (ArmCertValue.SubsShift64.tailX real x 5#5 5#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6272, 3390111942) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_65
  have pc : x.regs._PC = MemReloc.imageAddress base 6272 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    65 x inv.core (6272, 3390111942) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 65
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_65] using ob)
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6276, 3658547398) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_66
  have pc : x.regs._PC = MemReloc.imageAddress base 6276 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    66 x inv.core (6276, 3658547398) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 6#5 6#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 17), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 6#5 6#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 17), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 66
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpSbc64.selected 6#5 6#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 6), .reg (.x 17), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_66] using ob)
    (ArmCertValue.SecpSbc64.tailX real x 6#5 6#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6280, 3390046768) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_67
  have pc : x.regs._PC = MemReloc.imageAddress base 6280 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    67 x inv.core (6280, 3390046768) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 16#5 17#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.SecpEor64.tailX real x 16#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 16#5 17#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.SecpEor64.tailX real x 16#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 67
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 16#5 17#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_67] using ob)
    (ArmCertValue.SecpEor64.tailX real x 16#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6284, 2869494123) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_68
  have pc : x.regs._PC = MemReloc.imageAddress base 6284 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    68 x inv.core (6284, 2869494123) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 68
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 11#5 11#5 0#6 9#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 9), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_68] using ob)
    (ArmCertValue.AddsShift64.tailX real x 11#5 11#5 0#6 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6288, 3121217932) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_69
  have pc : x.regs._PC = MemReloc.imageAddress base 6288 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    69 x inv.core (6288, 3121217932) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 69
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 12#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_69] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 12#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6292, 3122594221) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_70
  have pc : x.regs._PC = MemReloc.imageAddress base 6292 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    70 x inv.core (6292, 3122594221) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 70
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_70] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6296, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_71
  have pc : x.regs._PC = MemReloc.imageAddress base 6296 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    71 x inv.core (6296, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 71
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_71] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6300, 2600828002) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_72
  have pc : x.regs._PC = MemReloc.imageAddress base 6300 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    72 x inv.core (6300, 2600828002) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 2#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Madd64.tailX real x 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 2#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Madd64.tailX real x 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 72
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 2#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.mul, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_72] using ob)
    (ArmCertValue.Madd64.tailX real x 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6304, 2613410929) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_73
  have pc : x.regs._PC = MemReloc.imageAddress base 6304 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    73 x inv.core (6304, 2613410929) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 17#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Umulh64.tailX real x 17#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 17#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Umulh64.tailX real x 17#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 73
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 17#5 3#5 5#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.umulh, [.reg (.x 3), .reg (.x 5)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_73] using ob)
    (ArmCertValue.Umulh64.tailX real x 17#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6308, 2600893583) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_74
  have pc : x.regs._PC = MemReloc.imageAddress base 6308 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    74 x inv.core (6308, 2600893583) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 74
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 15#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_74] using ob)
    (ArmCertValue.Madd64.tailX real x 15#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6312, 2613476481) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_75
  have pc : x.regs._PC = MemReloc.imageAddress base 6312 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    75 x inv.core (6312, 2613476481) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 1#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Umulh64.tailX real x 1#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 1#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Umulh64.tailX real x 1#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 75
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 1#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_75] using ob)
    (ArmCertValue.Umulh64.tailX real x 1#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6316, 3942842500) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_76
  have pc : x.regs._PC = MemReloc.imageAddress base 6316 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x inv.core (6316, 3942842500) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 76
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 4#5 4#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.sbc3, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 4), .reg (.x 3), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_76] using ob)
    (ArmCertValue.SubsShift64.tailX real x 4#5 4#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6320, 3666093188) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_77
  have pc : x.regs._PC = MemReloc.imageAddress base 6320 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x inv.core (6320, 3666093188) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 77
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 4#5 4#5 4#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 4#5 4#5 4#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_77] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 4#5 4#5 4#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6324, 3667862505) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_78
  have pc : x.regs._PC = MemReloc.imageAddress base 6324 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    78 x inv.core (6324, 3667862505) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 9#5 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 9#5 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 78
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨(.cselc 2#4), [.flag 0, .flag 1, .flag 2, .flag 3, .lit 0#64, .lit 18446744073709551615#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_78] using ob)
    (ArmCertValue.SecpCsinv2ZZ.tailX real x 9#5 (by decide) (by decide) ⟨⟩) actual
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
  have member : (6328, 2870018543) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_79
  have pc : x.regs._PC = MemReloc.imageAddress base 6328 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    79 x inv.core (6328, 2870018543) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 17#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 17#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 79
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 15#5 15#5 0#6 17#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 17), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_79] using ob)
    (ArmCertValue.AddsShift64.tailX real x 15#5 15#5 0#6 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6332, 2585722913) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_80
  have pc : x.regs._PC = MemReloc.imageAddress base 6332 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    80 x inv.core (6332, 2585722913) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 80
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_80] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6336, 3943039142) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_81
  have pc : x.regs._PC = MemReloc.imageAddress base 6336 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    81 x inv.core (6336, 3943039142) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 6#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.SubsShift64.tailX real x 6#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 6#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.SubsShift64.tailX real x 6#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 81
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 6#5 5#5 0#6 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.sbc3, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 5), .reg (.x 6), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_81] using ob)
    (ArmCertValue.SubsShift64.tailX real x 6#5 5#5 0#6 6#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6340, 3666224326) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_82
  have pc : x.regs._PC = MemReloc.imageAddress base 6340 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    82 x inv.core (6340, 3666224326) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 6#5 6#5 6#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 6#5 6#5 6#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 6#5 6#5 6#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 6#5 6#5 6#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 6#5 6#5 6#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 6#5 6#5 6#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 82
    (by decide) page (by decide) (N1D226.CsnegCs64Generic.Encoding.selected 6#5 6#5 6#5) _ (x.regs._PC + 4#64)
    (N1D226.CsnegCs64Generic.Value.upd x 6#5 6#5 6#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_82] using ob)
    (N1D226.CsnegCs64Generic.Value.tailX real x 6#5 6#5 6#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6344, 3666420009) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_83
  have pc : x.regs._PC = MemReloc.imageAddress base 6344 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    83 x inv.core (6344, 3666420009) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 9#5 9#5 9#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 9#5 9#5 9#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 9#5 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 9#5 9#5 9#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 9#5 9#5 9#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 9#5 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 83
    (by decide) page (by decide) (N1D226.CsinvCs64Generic.Encoding.selected 9#5 9#5 9#5) _ (x.regs._PC + 4#64)
    (N1D226.CsinvCs64Generic.Value.upd x 9#5 9#5 9#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_83] using ob)
    (N1D226.CsinvCs64Generic.Value.tailX real x 9#5 9#5 9#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6348, 2600893573) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_84
  have pc : x.regs._PC = MemReloc.imageAddress base 6348 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    84 x inv.core (6348, 2600893573) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 5#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.Madd64.tailX real x 5#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 5#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.Madd64.tailX real x 5#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 84
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 5#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.mul, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_84] using ob)
    (ArmCertValue.Madd64.tailX real x 5#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6352, 2613476486) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_85
  have pc : x.regs._PC = MemReloc.imageAddress base 6352 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    85 x inv.core (6352, 2613476486) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 85
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 6#5 4#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.umulh, [.reg (.x 4), .reg (.x 6)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_85] using ob)
    (ArmCertValue.Umulh64.tailX real x 6#5 4#5 6#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6356, 2869887057) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_86
  have pc : x.regs._PC = MemReloc.imageAddress base 6356 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    86 x inv.core (6356, 2869887057) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 17#5 2#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.AddsShift64.tailX real x 17#5 2#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 17#5 2#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.AddsShift64.tailX real x 17#5 2#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 86
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 17#5 2#5 0#6 15#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 15), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_86] using ob)
    (ArmCertValue.AddsShift64.tailX real x 17#5 2#5 0#6 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6360, 3120628207) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_87
  have pc : x.regs._PC = MemReloc.imageAddress base 6360 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    87 x inv.core (6360, 3120628207) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 1#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 1#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 87
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 15#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 1), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_87] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 15#5 1#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6364, 2585722913) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_88
  have pc : x.regs._PC = MemReloc.imageAddress base 6364 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    88 x inv.core (6364, 2585722913) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 88
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_88] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 1#5 1#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6368, 2969568575) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_89
  have pc : x.regs._PC = MemReloc.imageAddress base 6368 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    89 x inv.core (6368, 2969568575) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 9#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 9#5 1#12 (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 9#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 9#5 1#12 (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 89
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 9#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 9), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_89] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 9#5 1#12 (by decide)) actual
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
  have member : (6372, 3389587621) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_90
  have pc : x.regs._PC = MemReloc.imageAddress base 6372 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    90 x inv.core (6372, 3389587621) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 90
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 5#5 5#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.eor, [.reg (.x 5), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_90] using ob)
    (ArmCertValue.SecpEor64.tailX real x 5#5 5#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6376, 3121676465) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_91
  have pc : x.regs._PC = MemReloc.imageAddress base 6376 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    91 x inv.core (6376, 3121676465) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 17#5 5#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.Adcs64.tailX real x 17#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 17#5 5#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.Adcs64.tailX real x 17#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 91
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 17#5 5#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.add3Z, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.carry3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩, ⟨.ovf3, [.reg (.x 5), .reg (.x 17), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_91] using ob)
    (ArmCertValue.Adcs64.tailX real x 17#5 5#5 17#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6380, 3389587654) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_92
  have pc : x.regs._PC = MemReloc.imageAddress base 6380 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    92 x inv.core (6380, 3389587654) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 92
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 6#5 6#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.eor, [.reg (.x 6), .reg (.x 9)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_92] using ob)
    (ArmCertValue.SecpEor64.tailX real x 6#5 6#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6384, 3121545423) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_93
  have pc : x.regs._PC = MemReloc.imageAddress base 6384 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    93 x inv.core (6384, 3121545423) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 93
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 15#5 6#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.add3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.add3Z, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.carry3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩, ⟨.ovf3, [.reg (.x 6), .reg (.x 15), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_93] using ob)
    (ArmCertValue.Adcs64.tailX real x 15#5 6#5 15#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6388, 2584281121) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_94
  have pc : x.regs._PC = MemReloc.imageAddress base 6388 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    94 x inv.core (6388, 2584281121) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 1#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .reg (.x 9), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.Adc64.tailX real x 1#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 1#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .reg (.x 9), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.Adc64.tailX real x 1#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 94
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 1#5 1#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.add3, [.reg (.x 1), .reg (.x 9), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_94] using ob)
    (ArmCertValue.Adc64.tailX real x 1#5 1#5 9#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6392, 2869363049) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_95
  have pc : x.regs._PC = MemReloc.imageAddress base 6392 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    95 x inv.core (6392, 2869363049) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 11#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 11#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 95
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 9#5 11#5 0#6 7#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 11), .reg (.x 7), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_95] using ob)
    (ArmCertValue.AddsShift64.tailX real x 9#5 11#5 0#6 7#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6396, 3121086858) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_96
  have pc : x.regs._PC = MemReloc.imageAddress base 6396 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    96 x inv.core (6396, 3121086858) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 12#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 12#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 12#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 12#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 96
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 12#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.add3Z, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.carry3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩, ⟨.ovf3, [.reg (.x 12), .reg (.x 8), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_96] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 12#5 8#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6400, 3121283499) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_97
  have pc : x.regs._PC = MemReloc.imageAddress base 6400 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    97 x inv.core (6400, 3121283499) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 13#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 13#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 97
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 13#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_97] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 13#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6404, 3121349068) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_98
  have pc : x.regs._PC = MemReloc.imageAddress base 6404 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    98 x inv.core (6404, 3121349068) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 98
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 14#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_98] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 14#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 98
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 14#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_98] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 14#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 98
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 14#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 14), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_98] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 14#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6408, 3122594221) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_99
  have pc : x.regs._PC = MemReloc.imageAddress base 6408 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    99 x inv.core (6408, 3122594221) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 99
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_99] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 99
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_99] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 99
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 13#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_99] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 13#5 13#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6412, 2585723342) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_100
  have pc : x.regs._PC = MemReloc.imageAddress base 6412 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    100 x inv.core (6412, 2585723342) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_100] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_100] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 100
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64ZRm.selected 14#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_100] using ob)
    (ArmCertValue.Adc64ZRm.tailX real x 14#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6416, 2969568799) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_101
  have pc : x.regs._PC = MemReloc.imageAddress base 6416 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    101 x inv.core (6416, 2969568799) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 101
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_101] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 101
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_101] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 101
    (by decide) page (by decide) (N1D226.CmnImm64Generic.Encoding.selected 16#5 1#12) _ (x.regs._PC + 4#64)
    [] (some (⟨.add3N, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.carry3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 16), .lit 1#64, .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_101] using ob)
    (N1D226.CmnImm64Generic.Value.tailX real x 16#5 1#12 (by decide)) actual
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
  have member : (6420, 3390046274) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_102
  have pc : x.regs._PC = MemReloc.imageAddress base 6420 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    102 x inv.core (6420, 3390046274) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 102
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 2#5 2#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.eor, [.reg (.x 2), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_102] using ob)
    (ArmCertValue.SecpEor64.tailX real x 2#5 2#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 102
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 2#5 2#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.eor, [.reg (.x 2), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_102] using ob)
    (ArmCertValue.SecpEor64.tailX real x 2#5 2#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 102
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 2#5 2#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨.eor, [.reg (.x 2), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_102] using ob)
    (ArmCertValue.SecpEor64.tailX real x 2#5 2#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6424, 3121152073) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_103
  have pc : x.regs._PC = MemReloc.imageAddress base 6424 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    103 x inv.core (6424, 3121152073) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 103
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 2#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_103] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 2#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 103
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 2#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_103] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 2#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 103
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 2#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.add3Z, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.carry3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩, ⟨.ovf3, [.reg (.x 2), .reg (.x 9), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_103] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 2#5 9#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6428, 3390046769) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_104
  have pc : x.regs._PC = MemReloc.imageAddress base 6428 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    104 x inv.core (6428, 3390046769) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 104
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 17#5 17#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_104] using ob)
    (ArmCertValue.SecpEor64.tailX real x 17#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 104
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 17#5 17#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_104] using ob)
    (ArmCertValue.SecpEor64.tailX real x 17#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 104
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 17#5 17#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.eor, [.reg (.x 17), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_104] using ob)
    (ArmCertValue.SecpEor64.tailX real x 17#5 17#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6432, 3121218090) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_105
  have pc : x.regs._PC = MemReloc.imageAddress base 6432 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    105 x inv.core (6432, 3121218090) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 105
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 17#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_105] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 17#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 105
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 17#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_105] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 17#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 105
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 17#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.add3Z, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.carry3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩, ⟨.ovf3, [.reg (.x 17), .reg (.x 10), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_105] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 17#5 10#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6436, 3390046703) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_106
  have pc : x.regs._PC = MemReloc.imageAddress base 6436 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    106 x inv.core (6436, 3390046703) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 106
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_106] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 106
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_106] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 106
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 15#5 15#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.eor, [.reg (.x 15), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_106] using ob)
    (ArmCertValue.SecpEor64.tailX real x 15#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6440, 3121283563) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_107
  have pc : x.regs._PC = MemReloc.imageAddress base 6440 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    107 x inv.core (6440, 3121283563) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 107
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_107] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 107
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_107] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 107
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 11#5 15#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 15), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_107] using ob)
    (ArmCertValue.Adcs64.tailX real x 11#5 15#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6444, 3390046241) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_108
  have pc : x.regs._PC = MemReloc.imageAddress base 6444 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    108 x inv.core (6444, 3390046241) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 108
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 1#5 1#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.eor, [.reg (.x 1), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_108] using ob)
    (ArmCertValue.SecpEor64.tailX real x 1#5 1#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 108
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 1#5 1#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.eor, [.reg (.x 1), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_108] using ob)
    (ArmCertValue.SecpEor64.tailX real x 1#5 1#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 108
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpEor64.selected 1#5 1#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.eor, [.reg (.x 1), .reg (.x 16)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_108] using ob)
    (ArmCertValue.SecpEor64.tailX real x 1#5 1#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6448, 3121348652) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_109
  have pc : x.regs._PC = MemReloc.imageAddress base 6448 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    109 x inv.core (6448, 3121348652) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 109
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 1#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_109] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 1#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 109
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 1#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_109] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 1#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 109
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 12#5 1#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.add3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 1), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_109] using ob)
    (ArmCertValue.Adcs64.tailX real x 12#5 1#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6452, 3121611181) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_110
  have pc : x.regs._PC = MemReloc.imageAddress base 6452 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    110 x inv.core (6452, 3121611181) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 110
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_110] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 110
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_110] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 110
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 13#5 13#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.add3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.add3Z, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.carry3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩, ⟨.ovf3, [.reg (.x 13), .reg (.x 16), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_110] using ob)
    (ArmCertValue.Adcs64.tailX real x 13#5 13#5 16#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6456, 2584740302) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_111
  have pc : x.regs._PC = MemReloc.imageAddress base 6456 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    111 x inv.core (6456, 2584740302) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 111
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_111] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 111
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_111] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 111
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 14#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 14), .reg (.x 16), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_111] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 14#5 16#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6460, 3531635248) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_112
  have pc : x.regs._PC = MemReloc.imageAddress base 6460 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    112 x inv.core (6460, 3531635248) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 112
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 16#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_112] using ob)
    (ArmCertValue.Movz64z.tailX real x 16#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 112
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 16#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_112] using ob)
    (ArmCertValue.Movz64z.tailX real x 16#5 977#16 (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 112
    (by decide) page (by decide) (NativeEntryBodyDispatch.Movz64z.selected 16#5 977#16) _ (x.regs._PC + 4#64)
    [((.x 16), some ⟨(.const 977#64), []⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_112] using ob)
    (ArmCertValue.Movz64z.tailX real x 16#5 977#16 (by decide) (by decide) ⟨⟩) actual
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
  have member : (6464, 2992636417) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_113
  have pc : x.regs._PC = MemReloc.imageAddress base 6464 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    113 x inv.core (6464, 2992636417) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 113
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 1#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.orr, [.reg (.x 16), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_113] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 1#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 113
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 1#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.orr, [.reg (.x 16), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_113] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 1#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 113
    (by decide) page (by decide) (NativeEntryBodyDispatch.OrrImm32_0.selected 1#5 16#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨.orr, [.reg (.x 16), .lit 4294967296#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_113] using ob)
    (ArmCertValue.OrrImm32_0.tailX real x 1#5 16#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6468, 2601221155) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_114
  have pc : x.regs._PC = MemReloc.imageAddress base 6468 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    114 x inv.core (6468, 2601221155) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 114
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_114] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 114
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_114] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 114
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 1#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 1), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_114] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6472, 2613804069) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_115
  have pc : x.regs._PC = MemReloc.imageAddress base 6472 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    115 x inv.core (6472, 2613804069) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 115
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 1#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 1), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_115] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 115
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 1#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 1), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_115] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 115
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 5#5 1#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 5), some ⟨.umulh, [.reg (.x 1), .reg (.x 11)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_115] using ob)
    (ArmCertValue.Umulh64.tailX real x 5#5 1#5 11#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6476, 2453699983) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_116
  have pc : x.regs._PC = MemReloc.imageAddress base 6476 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    116 x inv.core (6476, 2453699983) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 116
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 12), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_116] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 116
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 12), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_116] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 116
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 12), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_116] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6480, 3546348930) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_117
  have pc : x.regs._PC = MemReloc.imageAddress base 6480 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    117 x inv.core (6480, 3546348930) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 117
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_117] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 2#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 117
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_117] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 2#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 117
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 12)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_117] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 2#5 12#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6484, 2601483780) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_118
  have pc : x.regs._PC = MemReloc.imageAddress base 6484 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    118 x inv.core (6484, 2601483780) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 118
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 16#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_118] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 118
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 16#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_118] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 118
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 4#5 16#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_118] using ob)
    (ArmCertValue.Madd64.tailX real x 4#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6488, 2600615439) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_119
  have pc : x.regs._PC = MemReloc.imageAddress base 6488 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    119 x inv.core (6488, 2600615439) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 119
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_119] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 119
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_119] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 119
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_119] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6492, 2869919876) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_120
  have pc : x.regs._PC = MemReloc.imageAddress base 6492 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    120 x inv.core (6492, 2869919876) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 120
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 32#6 15#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 32#6 15#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_120] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 32#6 15#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 120
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 32#6 15#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 32#6 15#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_120] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 32#6 15#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 120
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 4#5 4#5 32#6 15#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 4#5 4#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 4#5 32#6 15#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_120] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 4#5 4#5 32#6 15#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6496, 3546349039) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_121
  have pc : x.regs._PC = MemReloc.imageAddress base 6496 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    121 x inv.core (6496, 3546349039) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 121
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_121] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 121
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_121] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 121
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_121] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6500, 2584674374) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_122
  have pc : x.regs._PC = MemReloc.imageAddress base 6500 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    122 x inv.core (6500, 2584674374) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 122
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 2#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_122] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 122
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 2#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_122] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 122
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 6#5 2#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 6), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_122] using ob)
    (ArmCertValue.Adc64.tailX real x 6#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6504, 2601352235) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_123
  have pc : x.regs._PC = MemReloc.imageAddress base 6504 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    123 x inv.core (6504, 2601352235) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 123
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 1#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 1), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_123] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 123
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 1#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 1), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_123] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 123
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 11#5 1#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.mul, [.reg (.x 1), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_123] using ob)
    (ArmCertValue.Madd64.tailX real x 11#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6508, 2613935149) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_124
  have pc : x.regs._PC = MemReloc.imageAddress base 6508 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    124 x inv.core (6508, 2613935149) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 124
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 1#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 1), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_124] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 124
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 1#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 1), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_124] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 124
    (by decide) page (by decide) (NativeEntryBodyDispatch.Umulh64.selected 13#5 1#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 13), some ⟨.umulh, [.reg (.x 1), .reg (.x 13)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_124] using ob)
    (ArmCertValue.Umulh64.tailX real x 13#5 1#5 13#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6512, 2453700047) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_125
  have pc : x.regs._PC = MemReloc.imageAddress base 6512 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    125 x inv.core (6512, 2453700047) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 125
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 14), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_125] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 125
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 14), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_125] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 125
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpAndMask32.selected 15#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨.and, [.reg (.x 14), .lit 4294967295#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_125] using ob)
    (ArmCertValue.SecpAndMask32.tailX real x 15#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6516, 3546348994) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_126
  have pc : x.regs._PC = MemReloc.imageAddress base 6516 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    126 x inv.core (6516, 3546348994) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 126
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_126] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 2#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 126
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_126] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 2#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 126
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 2#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 2), some ⟨(.lsr 32), [.reg (.x 14)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_126] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 2#5 14#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6520, 2601483788) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_127
  have pc : x.regs._PC = MemReloc.imageAddress base 6520 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    127 x inv.core (6520, 2601483788) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 127
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_127] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 127
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_127] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 127
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 12#5 16#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 12), some ⟨.mul, [.reg (.x 16), .reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_127] using ob)
    (ArmCertValue.Madd64.tailX real x 12#5 16#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6524, 2600615439) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_128
  have pc : x.regs._PC = MemReloc.imageAddress base 6524 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    128 x inv.core (6524, 2600615439) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 128
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_128] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 128
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_128] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 128
    (by decide) page (by decide) (N1D226.Madd64Generic.Encoding.selected 15#5 16#5 15#5 2#5) _ (x.regs._PC + 4#64)
    (N1D226.Madd64Generic.DriverValue.upd x 15#5 16#5 15#5 2#5) (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_128] using ob)
    (N1D226.Madd64Generic.DriverValue.tailX real x 15#5 16#5 15#5 2#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6528, 2869920140) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_129
  have pc : x.regs._PC = MemReloc.imageAddress base 6528 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    129 x inv.core (6528, 2869920140) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 129
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 32#6 15#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 32#6 15#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_129] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 32#6 15#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 129
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 32#6 15#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 32#6 15#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_129] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 32#6 15#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 129
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 12#5 12#5 32#6 15#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 12#5 12#5 32#6 15#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 12#5 32#6 15#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_129] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 12#5 12#5 32#6 15#5 (by decide) (by decide) (by decide)) actual
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
  have member : (6532, 3546349039) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_130
  have pc : x.regs._PC = MemReloc.imageAddress base 6532 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    130 x inv.core (6532, 3546349039) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 130
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_130] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 130
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_130] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 130
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 15#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 15), some ⟨(.lsr 32), [.reg (.x 15)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_130] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 15#5 15#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6536, 2584674382) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_131
  have pc : x.regs._PC = MemReloc.imageAddress base 6536 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    131 x inv.core (6536, 2584674382) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 131
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 2#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_131] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 131
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 2#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_131] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 131
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 14#5 2#5 15#5) _ (x.regs._PC + 4#64)
    [((.x 14), some ⟨.add3, [.reg (.x 2), .reg (.x 15), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_131] using ob)
    (ArmCertValue.Adc64.tailX real x 14#5 2#5 15#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
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
  have member : (6540, 2869100775) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_132
  have pc : x.regs._PC = MemReloc.imageAddress base 6540 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    132 x inv.core (6540, 2869100775) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 132
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_132] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 132
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_132] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 132
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_132] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6544, 3120824584) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_133
  have pc : x.regs._PC = MemReloc.imageAddress base 6544 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    133 x inv.core (6544, 3120824584) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 133
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_133] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 133
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_133] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 133
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_133] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6548, 3121283369) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_134
  have pc : x.regs._PC = MemReloc.imageAddress base 6548 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    134 x inv.core (6548, 3121283369) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 134
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_134] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 134
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_134] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 134
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 11#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 11), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_134] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 11#5 (by decide) (by decide) (by decide) (by decide)) actual
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
  have member : (6552, 3121348938) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_135
  have pc : x.regs._PC = MemReloc.imageAddress base 6552 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    135 x inv.core (6552, 3121348938) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 135
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_135] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 135
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_135] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 135
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 12#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 12), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_135] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 12#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_136 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 136 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6556, 2594125803) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_136
  have pc : x.regs._PC = MemReloc.imageAddress base 6556 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    136 x inv.core (6556, 2594125803) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 136
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_136] using ob)
    (ArmCertValue.Csinc3.tailX real x 11#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 136
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_136] using ob)
    (ArmCertValue.Csinc3.tailX real x 11#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 136
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csinc3.selected 11#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨(.cond 2#4), [.flag 0, .flag 1, .flag 2, .flag 3]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_136] using ob)
    (ArmCertValue.Csinc3.tailX real x 11#5 (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_137 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 137 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6560, 2869231880) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_137
  have pc : x.regs._PC = MemReloc.imageAddress base 6560 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    137 x inv.core (6560, 2869231880) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 137
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 5#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_137] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 137
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 5#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_137] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 137
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 8#5 8#5 0#6 5#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 5), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_137] using ob)
    (ArmCertValue.AddsShift64.tailX real x 8#5 8#5 0#6 5#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_138 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 138 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6564, 3120955689) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_138
  have pc : x.regs._PC = MemReloc.imageAddress base 6564 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    138 x inv.core (6564, 3120955689) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 138
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_138] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 138
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_138] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 138
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 9#5 9#5 6#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .reg (.x 6), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_138] using ob)
    (ArmCertValue.Adcs64.tailX real x 9#5 9#5 6#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_139 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 139 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6568, 3121414474) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_139
  have pc : x.regs._PC = MemReloc.imageAddress base 6568 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    139 x inv.core (6568, 3121414474) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 139
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_139] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 139
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_139] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 139
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 10#5 10#5 13#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .reg (.x 13), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_139] using ob)
    (ArmCertValue.Adcs64.tailX real x 10#5 10#5 13#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_140 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 140 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6572, 2584609131) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_140
  have pc : x.regs._PC = MemReloc.imageAddress base 6572 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    140 x inv.core (6572, 2584609131) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 140
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 11#5 11#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_140] using ob)
    (ArmCertValue.Adc64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 140
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 11#5 11#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_140] using ob)
    (ArmCertValue.Adc64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 140
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adc64.selected 11#5 11#5 14#5) _ (x.regs._PC + 4#64)
    [((.x 11), some ⟨.add3, [.reg (.x 11), .reg (.x 14), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_140] using ob)
    (ArmCertValue.Adc64.tailX real x 11#5 11#5 14#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_141 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 141 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6576, 2432697713) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_141
  have pc : x.regs._PC = MemReloc.imageAddress base 6576 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    141 x inv.core (6576, 2432697713) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 141
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 17#5 11#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add, [.reg (.x 11), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_141] using ob)
    (ArmCertValue.AddImm64.tailX real x 17#5 11#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 141
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 17#5 11#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add, [.reg (.x 11), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_141] using ob)
    (ArmCertValue.AddImm64.tailX real x 17#5 11#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 141
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddImm64.selected 17#5 11#5 1#12) _ (x.regs._PC + 4#64)
    [((.x 17), some ⟨.add, [.reg (.x 11), .lit 1#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_141] using ob)
    (ArmCertValue.AddImm64.tailX real x 17#5 11#5 1#12 (rd := by decide) (rn := by decide) (noEret := by decide) (profile := ⟨⟩)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_142 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 142 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6580, 2601614851) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_142
  have pc : x.regs._PC = MemReloc.imageAddress base 6580 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    142 x inv.core (6580, 2601614851) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 142
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 16#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 16), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_142] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 16#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 142
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 16#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 16), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_142] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 16#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 142
    (by decide) page (by decide) (NativeEntryBodyDispatch.Madd64.selected 3#5 16#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 3), some ⟨.mul, [.reg (.x 16), .reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_142] using ob)
    (ArmCertValue.Madd64.tailX real x 3#5 16#5 17#5 (by decide) (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_143 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 143 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6584, 3546349092) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_143
  have pc : x.regs._PC = MemReloc.imageAddress base 6584 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    143 x inv.core (6584, 3546349092) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 143
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 4#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨(.lsr 32), [.reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_143] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 4#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 143
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 4#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨(.lsr 32), [.reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_143] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 4#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 143
    (by decide) page (by decide) (NativeEntryBodyDispatch.SecpLsr32.selected 4#5 17#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨(.lsr 32), [.reg (.x 17)]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_143] using ob)
    (ArmCertValue.SecpLsr32.tailX real x 4#5 17#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_144 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 144 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6588, 2870050915) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_144
  have pc : x.regs._PC = MemReloc.imageAddress base 6588 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    144 x inv.core (6588, 2870050915) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 144
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 3#5 3#5 32#6 17#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 3#5 3#5 32#6 17#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 3#5 32#6 17#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_144] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 3#5 3#5 32#6 17#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 144
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 3#5 3#5 32#6 17#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 3#5 3#5 32#6 17#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 3#5 32#6 17#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_144] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 3#5 3#5 32#6 17#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 144
    (by decide) page (by decide) (N1D226.AddsShift64Generic.Encoding.selected 3#5 3#5 32#6 17#5) _ (x.regs._PC + 4#64)
    (N1D226.AddsShift64Generic.Value.upd x 3#5 3#5 32#6 17#5) ((N1D226.AddsShift64Generic.Value.flag_updates x 3#5 32#6 17#5)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_144] using ob)
    (N1D226.AddsShift64Generic.Value.tailX real x 3#5 3#5 32#6 17#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_145 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 145 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6592, 2583954404) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_145
  have pc : x.regs._PC = MemReloc.imageAddress base 6592 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    145 x inv.core (6592, 2583954404) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 145
    (by decide) page (by decide) (N1D226.AdcZeroRn64Generic.Encoding.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.lit 0#64, .reg (.x 4), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_145] using ob)
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 4#5 4#5 (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 145
    (by decide) page (by decide) (N1D226.AdcZeroRn64Generic.Encoding.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.lit 0#64, .reg (.x 4), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_145] using ob)
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 4#5 4#5 (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 145
    (by decide) page (by decide) (N1D226.AdcZeroRn64Generic.Encoding.selected 4#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 4), some ⟨.add3, [.lit 0#64, .reg (.x 4), .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_145] using ob)
    (N1D226.AdcZeroRn64Generic.Value.tailX real x 4#5 4#5 (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_146 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 146 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6596, 2869100775) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_146
  have pc : x.regs._PC = MemReloc.imageAddress base 6596 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    146 x inv.core (6596, 2869100775) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 146
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_146] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 146
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_146] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 146
    (by decide) page (by decide) (NativeEntryBodyDispatch.AddsShift64.selected 7#5 7#5 0#6 3#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.add3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)] (some (⟨.add3N, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.add3Z, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.carry3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩, ⟨.ovf3, [.reg (.x 7), .reg (.x 3), .lit 0#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_146] using ob)
    (ArmCertValue.AddsShift64.tailX real x 7#5 7#5 0#6 3#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_147 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 147 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6600, 3120824584) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_147
  have pc : x.regs._PC = MemReloc.imageAddress base 6600 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    147 x inv.core (6600, 3120824584) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 147
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_147] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 147
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_147] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 147
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64.selected 8#5 8#5 4#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.add3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.add3Z, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.carry3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩, ⟨.ovf3, [.reg (.x 8), .reg (.x 4), .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_147] using ob)
    (ArmCertValue.Adcs64.tailX real x 8#5 8#5 4#5 (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_148 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 148 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6604, 3122594089) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_148
  have pc : x.regs._PC = MemReloc.imageAddress base 6604 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    148 x inv.core (6604, 3122594089) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 148
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_148] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 148
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_148] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 148
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.add3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_148] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_149 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 149 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6608, 3122594122) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_149
  have pc : x.regs._PC = MemReloc.imageAddress base 6608 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    149 x inv.core (6608, 3122594122) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 149
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_149] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 149
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_149] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 149
    (by decide) page (by decide) (NativeEntryBodyDispatch.Adcs64ZRm.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.add3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (some (⟨.add3N, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.add3Z, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.carry3, [.reg (.x 10), .lit 0#64, .flag 2]⟩, ⟨.ovf3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_149] using ob)
    (ArmCertValue.Adcs64ZRm.tailX real x 10#5 10#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_150 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 150 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6612, 2594123809) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_150
  have pc : x.regs._PC = MemReloc.imageAddress base 6612 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    150 x inv.core (6612, 2594123809) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 150
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 1), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_150] using ob)
    (ArmCertValue.Csel3.tailX real x 1#5 1#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 150
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 1), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_150] using ob)
    (ArmCertValue.Csel3.tailX real x 1#5 1#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 150
    (by decide) page (by decide) (NativeEntryBodyDispatch.Csel3.selected 1#5 1#5) _ (x.regs._PC + 4#64)
    [((.x 1), some ⟨(.cselc 3#4), [.flag 0, .flag 1, .flag 2, .flag 3, .reg (.x 1), .lit 0#64]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_150] using ob)
    (ArmCertValue.Csel3.tailX real x 1#5 1#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_151 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 151 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6616, 3942711527) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_151
  have pc : x.regs._PC = MemReloc.imageAddress base 6616 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    151 x inv.core (6616, 3942711527) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 151
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 7#5 7#5 0#6 1#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_151] using ob)
    (ArmCertValue.SubsShift64.tailX real x 7#5 7#5 0#6 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 151
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 7#5 7#5 0#6 1#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_151] using ob)
    (ArmCertValue.SubsShift64.tailX real x 7#5 7#5 0#6 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 151
    (by decide) page (by decide) (NativeEntryBodyDispatch.SubsShift64.selected 7#5 7#5 0#6 1#5) _ (x.regs._PC + 4#64)
    [((.x 7), some ⟨.sbc3, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)] (some (⟨.sbc3N, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3Z, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3C, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩, ⟨.sbc3V, [.reg (.x 7), .reg (.x 1), .lit 1#64]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_151] using ob)
    (ArmCertValue.SubsShift64.tailX real x 7#5 7#5 0#6 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_152 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 152 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6620, 4196335880) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_152
  have pc : x.regs._PC = MemReloc.imageAddress base 6620 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    152 x inv.core (6620, 4196335880) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 152
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 8#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_152] using ob)
    (ArmCertValue.Sbcs64.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 152
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 8#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_152] using ob)
    (ArmCertValue.Sbcs64.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 152
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 8#5 8#5) _ (x.regs._PC + 4#64)
    [((.x 8), some ⟨.sbc3, [.reg (.x 8), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 8), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 8), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_152] using ob)
    (ArmCertValue.Sbcs64.tailX real x 8#5 8#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_153 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 153 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6624, 4196335913) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_153
  have pc : x.regs._PC = MemReloc.imageAddress base 6624 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    153 x inv.core (6624, 4196335913) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 153
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_153] using ob)
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 153
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_153] using ob)
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 153
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbcs64.selected 9#5 9#5) _ (x.regs._PC + 4#64)
    [((.x 9), some ⟨.sbc3, [.reg (.x 9), .lit 0#64, .flag 2]⟩)] (some (⟨.sbc3N, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3Z, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3C, [.reg (.x 9), .lit 0#64, .flag 2]⟩, ⟨.sbc3V, [.reg (.x 9), .lit 0#64, .flag 2]⟩)) x fin inv.core
    (by simpa only [DefaultScalarSites.word_153] using ob)
    (ArmCertValue.Sbcs64.tailX real x 9#5 9#5 (by decide) (by decide) (by decide)) actual
  exact ⟨fp,dit,ctl⟩

private theorem step_154 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 154 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have member : (6628, 3659465034) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? DefaultScalarSites.site_154
  have pc : x.regs._PC = MemReloc.imageAddress base 6628 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    154 x inv.core (6628, 3659465034) member pc
  have fp := FPControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 154
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_154] using ob)
    (ArmCertValue.Sbc64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have dit := DitShim243.DITFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 154
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_154] using ob)
    (ArmCertValue.Sbc64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
  have ctl := DitShim243.ControlFrame.scalar_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 154
    (by decide) page (by decide) (NativeEntryBodyDispatch.Sbc64.selected 10#5 10#5) _ (x.regs._PC + 4#64)
    [((.x 10), some ⟨.sbc3, [.reg (.x 10), .lit 0#64, .flag 2]⟩)] (none) x fin inv.core
    (by simpa only [DefaultScalarSites.word_154] using ob)
    (ArmCertValue.Sbc64.tailX real x 10#5 10#5 (by decide) (by decide) (by decide) ⟨⟩) actual
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
    change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (0+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 0 + 4#64 = offset EntryBinding.plan (0+1) from by decide)
  have memberCode : (6012, 2839547939) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_0
  have codePC : x.regs._PC = MemReloc.imageAddress base 6012 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x inv.core (6012, 2839547939) memberCode codePC
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
    change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (1+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 1 + 4#64 = offset EntryBinding.plan (1+1) from by decide)
  have memberCode : (6016, 2839550021) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_1
  have codePC : x.regs._PC = MemReloc.imageAddress base 6016 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x inv.core (6016, 2839550021) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_1 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_1] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[2]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_25 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_25 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 25 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (25+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 25 + 4#64 = offset EntryBinding.plan (25+1) from by decide)
  have memberCode : (6112, 2839613475) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_25
  have codePC : x.regs._PC = MemReloc.imageAddress base 6112 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    25 x inv.core (6112, 2839613475) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_25 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_25] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_25 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_25] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_25 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_25] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[3]? = some (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_26 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_26 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 26 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (26+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 26 + 4#64 = offset EntryBinding.plan (26+1) from by decide)
  have memberCode : (6116, 2839615557) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_26
  have codePC : x.regs._PC = MemReloc.imageAddress base 6116 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    26 x inv.core (6116, 2839615557) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_26 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_26] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_26 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_26] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_26 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 5#5 6#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 5#5 6#5 2#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_26] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[4]? = some (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_50 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_50 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (16)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 2 2#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 50 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (50+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 50 + 4#64 = offset EntryBinding.plan (50+1) from by decide)
  have memberCode : (6212, 2839613475) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_50
  have codePC : x.regs._PC = MemReloc.imageAddress base 6212 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    50 x inv.core (6212, 2839613475) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_50 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_50] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_50 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_50] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_50 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 3#5 4#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 3#5 4#5 2#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_50] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[5]? = some (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 1) 0 = entryGPR initial 1 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 1 (by decide)
  have pointer := PairData.memory_base_51 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_51 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 1) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 1#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 51 + DefaultBudget.cost (LdpBytes.pairAddr x 1#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (51+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 51 + 4#64 = offset EntryBinding.plan (51+1) from by decide)
  have memberCode : (6216, 2839560239) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_51
  have codePC : x.regs._PC = MemReloc.imageAddress base 6216 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    51 x inv.core (6216, 2839560239) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_51 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 15#5 16#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_51] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_51 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 15#5 16#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_51] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_51 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 15#5 16#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 1#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 15#5 16#5 0#7 1#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_51] using ob) fin actual
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
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[6]? = some (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 2) 0 = entryGPR initial 2 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 2 (by decide)
  have pointer := PairData.memory_base_55 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  obtain ⟨data,payload⟩ := PairData.load_payload_55 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
    (initial.regs.bank_BitVec_64 .TPIDR_EL0) (Default.inputs_length mapping initial) x inv.agrees
  have facts := DefaultSelectedPairFacts.load_facts (· ∈ addresses EntryBinding.plan base initial) mapping (rowsFootprint raw.imageRows).byte (sites EntryBinding.plan initial) (codeVAs EntryBinding.plan base)
    (⟨(BitVec.addInt (entryGPR initial 2) (0)), false⟩ : SelectedMap.Site) member (by rfl) (view EntryBinding.plan mapping initial) X 0 0#7 2#5 x source span targets data payload
  have cost : DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) = DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0)) := congrArg DefaultBudget.cost source
  have statusBound : DefaultState.drawsBefore initial 55 + DefaultBudget.cost (LdpBytes.pairAddr x 2#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (55+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 55 + 4#64 = offset EntryBinding.plan (55+1) from by decide)
  have memberCode : (6232, 2839561295) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_55
  have codePC : x.regs._PC = MemReloc.imageAddress base 6232 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    55 x inv.core (6232, 2839561295) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_55 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 15#5 17#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 15#5 17#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_55] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_55 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 15#5 17#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 15#5 17#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_55] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_55 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (fun _ _ _ _ h => h) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.ldp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 15#5 17#5 (by decide) (by decide) (by decide) (by decide) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.ldp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 2#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.ldp_xfer_pay mapping 15#5 17#5 0#7 2#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_55] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_155 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 155 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[7]? = some (⟨(BitVec.addInt (entryGPR initial 0) (0)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_155 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 155 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 0#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change ((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (155+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 155 + 4#64 = offset EntryBinding.plan (155+1) from by decide)
  have memberCode : (6632, 2835357703) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_155
  have codePC : x.regs._PC = MemReloc.imageAddress base 6632 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    155 x inv.core (6632, 2835357703) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_155 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 7#5 8#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_155] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_155 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 7#5 8#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_155] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_155 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 0#7 0#5 7#5 8#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 0#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 7#5 8#5 0#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_155] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_156 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 156 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have initialInv := receipt.initialInv
  have rams := receipt.targets
  have member : (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) ∈ (sites EntryBinding.plan initial) :=
    List.mem_of_getElem? (show (sites EntryBinding.plan initial)[8]? = some (⟨(BitVec.addInt (entryGPR initial 0) (16)), true⟩ : SelectedMap.Site) by rfl)
  have input : (Default.inputs mapping initial).getD (totalL rs_c00 + 0) 0 = entryGPR initial 0 :=
    SecpCurrentEntry.inputs_gpr EntryBinding.plan mapping initial 0 (by decide)
  have pointer := PairData.memory_base_156 (view EntryBinding.plan mapping initial) (Default.inputs mapping initial)
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
  have statusBound : DefaultState.drawsBefore initial 156 + DefaultBudget.cost (LdpBytes.pairAddr x 0#5 2#7) ≤ DefaultState.capacity initial := by
    rw [cost]
    change (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ≤ (((((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
    omega
  have next : x.regs._PC + 4#64 = base + offset EntryBinding.plan (156+1) := by
    rw [inv.core.v1.pc, BitVec.add_assoc]
    exact congrArg (base + ·) (show offset EntryBinding.plan 156 + 4#64 = offset EntryBinding.plan (156+1) from by decide)
  have memberCode : (6636, 2835425289) ∈ EntryBinding.plan.code := List.mem_of_getElem? DefaultPairSites.site_156
  have codePC : x.regs._PC = MemReloc.imageAddress base 6636 := by rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    156 x inv.core (6636, 2835425289) memberCode codePC
  have fp := FPControlFrame.memory_step real inv (DefaultState.budget_room_156 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 9#5 10#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 9#5 10#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_156] using ob) fin actual
  have dit := DitShim243.DITFrame.memory_step real inv (DefaultState.budget_room_156 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 9#5 10#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 9#5 10#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_156] using ob) fin actual
  have ctl := DitShim243.ControlFrame.memory_step real inv (DefaultState.budget_room_156 initial)
    statusBound (by decide) page (by decide)
    (fun o pa inside mapped inTable => layout.separated o pa inside mapped (Or.inl inTable))
    (SecpCurrentEntry.code_output EntryBinding.plan raw mapping base initial layout) (fun _ c => PairDefault236.Ctx.of_finite c)
    (DefaultPairSelected.stp_tailG real (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping (consumer EntryBinding.plan raw mapping base initial) 2#7 0#5 9#5 10#5 (by decide) (by decide) (by decide) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) x (profile initial) inv.core.profileAt)
    (fun _ g _ mm => DefaultPairSelected.stp_xfer_facts (· ∈ addresses EntryBinding.plan base initial) (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) mapping (consumer EntryBinding.plan raw mapping base initial) (fun pa => pa ∈ outputBytes EntryBinding.plan mapping initial) 2#7 0#5 g mm facts)
    (fun _ _ g sp mm nz pay => DefaultPairSelected.stp_xfer_pay mapping 9#5 10#5 2#7 0#5 g sp mm nz pay)
    next (by simpa only [DefaultPairSites.word_156] using ob) fin actual
  exact ⟨fp,dit,ctl⟩

private theorem step_157 (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial)
    (page : base.toNat % 4096 = 0)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 157 x)
    (actual : modelStep real x = .ok () fin) :
    (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have low := receipt.low
  have original := DefaultTerminal.original_lr mapping initial x inv.agrees
  have currentLow : (x.regs.gpr[(GPRSummary.key (30#5).toNat).val]).toNat < 2 ^ 55 := by
    rw [original]; exact low
  have member : (6640, 0xd65f03c0) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[157]? = some (6640, 0xd65f03c0) from rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 6640 := by
    rw [inv.core.v1.pc]; rfl
  have ob := DitShim243.RawFetch.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial (EntryBinding.plan.code.length + 4) rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0))
    (fun c member i hi => ImageBinding.code_image base member i hi)
    157 x inv.core (6640, 0xd65f03c0) member pc
  have fp := FPControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 157
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have dit := DitShim243.DITFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 157
    (by decide) page (by decide) x fin inv.core inv.branch (30#5) (by decide) (by decide) currentLow
    (by simpa only [show ArmBridge.CruxGenGuarded.EntryBodyRet.W (30#5) = 0xd65f03c0#32 from by decide] using ob)
    actual
  have ctl := DitShim243.ControlFrame.ret_step real (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping
    (consumer EntryBinding.plan raw mapping base initial) (· ∈ codeOffsets EntryBinding.plan)
    (referenceImageI SecpArtifact.elf base (fun _ => 0)) base
    base (offset EntryBinding.plan) (EntryBinding.plan.code.length + 4)
    (profile initial) catalogue 157
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
    (k : Nat) (bound : k < 158)
    (x fin : NativeState) (inv : DitBodyState.Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue k x)
    (actual : modelStep real x = .ok () fin) : (fin.regs.FPCR = x.regs.FPCR ∧ fin.regs.FPSR = x.regs.FPSR) ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ RtPremC.ctlv fin.regs = RtPremC.ctlv x.regs := by
  have selected : k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157] : List Nat) := by
    change k ∈ List.range 158
    exact List.mem_range.mpr bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127 | h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143 | h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157
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
  · subst k; exact step_136 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_137 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_138 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_139 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_140 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_141 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_142 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_143 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_144 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_145 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_146 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_147 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_148 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_149 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_150 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_151 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_152 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_153 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_154 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_155 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_156 real raw config rows mapping base initial topology layout page receipt x fin inv actual
  · subst k; exact step_157 real raw config rows mapping base initial topology layout page receipt x fin inv actual

theorem preserves (real : Type) [Sail.SailReal real]
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue}
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (receipt : DitBodyState.Receipt raw config rows mapping base initial catalogue topology) :
    ∀ k, k ≤ 158 →
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
end PipeLean_D234_SecpMul_c15.DitBodyFrames
