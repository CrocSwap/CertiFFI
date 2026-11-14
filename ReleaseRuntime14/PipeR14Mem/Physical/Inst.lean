-- physical-byte invariants, old program constants reused unchanged.
import PipeR14.Inst
import ArmCertPipe.PhysicalDeploy
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmCert.Translate.Model.StaticPie
set_option autoImplicit false
namespace PipeR14.Physical
open ArmCertValue

abbrev Inv_c00 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c00 R14Plan.codeWords_c00 R14Plan.entry_c00 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c00 budget bytePA regions_c00 σ0_c00 inputs plan_c00

abbrev Inv_c01 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c01 R14Plan.codeWords_c01 R14Plan.entry_c01 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c01 budget bytePA regions_c01 σ0_c01 inputs plan_c01

abbrev Inv_c02 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c02 R14Plan.codeWords_c02 R14Plan.entry_c02 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c02 budget bytePA regions_c02 σ0_c02 inputs plan_c02

abbrev Inv_c03 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c03 R14Plan.codeWords_c03 R14Plan.entry_c03 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c03 budget bytePA regions_c03 σ0_c03 inputs plan_c03

abbrev Inv_c04 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c04 R14Plan.codeWords_c04 R14Plan.entry_c04 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c04 budget bytePA regions_c04 σ0_c04 inputs plan_c04

abbrev Inv_c05 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c05 R14Plan.codeWords_c05 R14Plan.entry_c05 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c05 budget bytePA regions_c05 σ0_c05 inputs plan_c05

abbrev Inv_c06 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c06 R14Plan.codeWords_c06 R14Plan.entry_c06 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c06 budget bytePA regions_c06 σ0_c06 inputs plan_c06

abbrev Inv_c07 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c07 R14Plan.codeWords_c07 R14Plan.entry_c07 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c07 budget bytePA regions_c07 σ0_c07 inputs plan_c07

abbrev Inv_c08 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c08 R14Plan.codeWords_c08 R14Plan.entry_c08 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c08 budget bytePA regions_c08 σ0_c08 inputs plan_c08

abbrev Inv_c09 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c09 R14Plan.codeWords_c09 R14Plan.entry_c09 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c09 budget bytePA regions_c09 σ0_c09 inputs plan_c09

abbrev Inv_c10 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c10 R14Plan.codeWords_c10 R14Plan.entry_c10 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c10 budget bytePA regions_c10 σ0_c10 inputs plan_c10

abbrev Inv_c11 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c11 R14Plan.codeWords_c11 R14Plan.entry_c11 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c11 budget bytePA regions_c11 σ0_c11 inputs plan_c11

abbrev Inv_c12 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c12 budget bytePA regions_c12 σ0_c12 inputs plan_c12

abbrev Inv_c13 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop) (bytes : Array Nat)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins) (budget : Nat)
    (inputs : List (BitVec 64)) (bytePA : ArmCertValue.Physical.BytePA) : Nat → NativeState → Prop :=
  ArmCertPipe.Physical.InvG spec config rows mapping
    (R14E17.consumerMap R14Plan.accesses_c13 R14Plan.codeWords_c13 R14Plan.entry_c13 p base.toNat mapping table)
    sc (referenceImageI bytes base ifunc) base base offset_c13 budget bytePA regions_c13 σ0_c13 inputs plan_c13

end PipeR14.Physical
