-- Memory: per-class memory tails over the fetched-state context
-- (prem_<K> + mem_tailD_<K>) and the code-side fetch obligations of a memory step (as straight2).
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.StraightV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose ArmBridge.CruxGenGuarded.ChainInvV2
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace HeapV2StepCerts.MemNext
open HeapV2StepCerts.RegBind HeapV2StepCerts.C3

/-- Code side of a memory step (identical to straight2's placedNext / fetch fields). -/
theorem memNextPlaced
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (succ : offsetOf (k + 1) = BitVec.ofNat 64 (0x10278 + off + 4)) (x : NativeState)
    (inv : Inv2 spec config rows mapping pins table base budget k x) : x.regs._PC + 4#64 = base + offsetOf (k + 1) := by
  rw [inv.v1.pc, here, succ, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

def memFetch
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat) (x : NativeState)
    (inv : Inv2 spec config rows mapping pins table base budget k x) : FetchObligations spec config rows mapping w x :=
  have pcImage : x.regs._PC = MemReloc.imageAddress base (HeapV2.entryOffset + off) := by
    rw [inv.v1.pc, here]; rfl
  have pcCode : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC =
      HeapV2E17.codeVA base.toNat (off, wordNat).1 := by
    show x.regs._PC = _
    rw [pcImage, MemReloc.imageAddress, add_ofNat]
    simp only [HeapV2E17.codeVA, Nat.add_assoc]
  have facts := ArmBridge.CruxGenGuarded.EntryActualFetch.before_fetch_facts x
    (NativeEntryTail.EntryPins.of_scalar x inv.v1.pins) inv.v1.features inv.v1.debug
  have el := facts.2.1
  have mode := facts.2.2.2.2.2.2.1
  have ep := NativeEntryTail.EntryPins.of_scalar x inv.v1.pins
  have rme : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.FeatureImpl[232] = false := by
    show x.regs.FeatureImpl[232] = false; simpa using ep.rme
  have nrw : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.PSTATE.nRW = 0#1 := by
    show x.regs.PSTATE.nRW = 0#1; simpa using ep.nrw
  { queryOf := fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩
    rawOf := fun _ => rfl
    vaOf := fun _ => rfl
    mmio := by rw [pcImage]; exact static.notMMIO _ member
    present := mapped_bytes_present_of_image_on inv.placed pcImage
      (static.inside _ member) (static.contiguous _ member)
    perAcc := HeapV2E17.fetch_per_acc_el0 spec config rows mapping pins base.toNat table
      member pcCode inv.closed rme nrw inv.v1.features.b3 inv.v1.features.a3 el mode.ns
    code := by
      intro acc leafLevel view faultOut address translated w' clean bytes
      rw [wordEq]
      exact HeapV2E17.fetch_code spec config rows mapping (pre := ArmBridge.CruxGenGuarded.beforeFetchState x)
        member (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) inv.placed static.separated
        pcImage (static.inside _ member) (static.contiguous _ member) acc leafLevel view faultOut address
        translated w' clean bytes }

/-- The fetched-state context instance of the heap-v2 plan. -/
abbrev Ctx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (p : HeapV2E17.Pins) (base : Nat) (table : Nat → Prop) (k : Nat) : NativeState → Prop :=
  FetchedCtx spec config rows mapping (HeapV2E17.consumerMap p base mapping table) p k

theorem memV_Ldrb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    {r : Reg} (hat : accessAt e.1 = some (r, 0)) (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdrb Rn Rt imm9) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (dataBytes p mapping)
      (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) NativeEntryBodyMem.Ldrb.writes 631 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  obtain ⟨perAcc, pa, mapped, mmio, outside, v, byte⟩ :=
    prem_Ldrb fetched ctx.closed static ctx.present member ctx.regBind Rn hat hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inD⟩ :=
    MemTail.mem_tailD_Ldrb real spec config rows mapping source fetched enc0 imm9 Rn Rt hRn hRt hRnt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.dcache pa mapped mmio v byte outside (dataBytes p mapping) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inD, gic, pc, np, keep, holds⟩

theorem memV_Strb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Strb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    {r : Reg} (hat : accessAt e.1 = some (r, 0)) (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = true) (hupd : upds k = updStrb Rn imm9) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (dataBytes p mapping)
      (NativeEntryBodyDispatch.Strb.selected Rt Rn imm9) NativeEntryBodyMem.Strb.writes 649 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hva := base_va member ctx.regBind hat
  obtain ⟨perAcc, pa, mapped, mmio, outside⟩ :=
    prem_Strb fetched ctx.closed static ctx.post2 member ctx.regBind Rn hat hsize hw
  have inD : dataBytes p mapping pa.toNat :=
    ⟨e, member, _, pa.toNat, Or.inl hva, mapped, Nat.le_refl _, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Strb real spec config rows mapping source fetched enc0 imm9 Rn Rt hRn hRt hRnt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 pa mapped mmio outside (dataBytes p mapping) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memV_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (dataBytes p mapping)
      (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) NativeEntryBodyMem.Stp.writes 617 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    prem_Stp fetched ctx.closed static ctx.post2 pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  have inD : ∀ i < 16, dataBytes p mapping (pa.toNat + i) := fun i hi =>
    ⟨e, member, _, pa.toNat, Or.inl hva, mapped, by omega, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Stp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio outside (dataBytes p mapping) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memV_Ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (dataBytes p mapping)
      (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) NativeEntryBodyMem.Ldp.writes 611 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_Ldp fetched ctx.closed static ctx.present pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Ldp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (dataBytes p mapping) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memV_Stp8 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} {r : Reg} (hat : accessAt e.1 = some (r, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (dataBytes p mapping)
      (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) NativeEntryBodyMem.Stp8.writes 617 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hva : MemClass.Stp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e :=
    pair8_va member ctx.regBind Rn imm7 hat himm
  obtain ⟨perAcc, preW, h8, pa1, pa2, mapped1, mapped2, contiguous, mmio1, mmio2, outside1, outside2⟩ :=
    prem_Stp8 fetched ctx.closed static ctx.post2 pinAligned member ctx.regBind Rn imm7 hat himm hoff.2 hsize hw
  have inD1 : ∀ i < 8, dataBytes p mapping (pa1.toNat + i) := fun i hi =>
    ⟨e, member, _, pa1.toNat, Or.inl hva, mapped1, by omega, by rw [hsize]; omega⟩
  have inD2 : ∀ i < 8, dataBytes p mapping (pa2.toNat + i) := fun i hi =>
    ⟨e, member, _, pa2.toNat, Or.inr (by rw [hva]), mapped2, by omega, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Stp8 real spec config rows mapping source fetched enc0 imm7 Rn Rt Rt2 hRn hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc preW ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache h8 pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 outside1 outside2
      (dataBytes p mapping) inD1 inD2 ctx.raw (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

theorem memV_Ldp8 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} {r : Reg} (hat : accessAt e.1 = some (r, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (source : NativeState) :
    MemTailVAt real spec config rows (Ctx spec config rows mapping p base table k) (dataBytes p mapping)
      (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) NativeEntryBodyMem.Ldp8.writes 611 source
      (source.regs._PC + 4#64) (upds k) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  obtain ⟨perAcc, h8, pa1, pa2, mapped1, mapped2, contiguous, mmio1, mmio2, data, bytes1, bytes2⟩ :=
    prem_Ldp8 fetched ctx.closed static ctx.present pinAligned member ctx.regBind Rn imm7 hat himm hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Ldp8 real spec config rows mapping source fetched enc0 imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache h8 pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 data bytes1 bytes2
      (dataBytes p mapping) ctx.raw (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

#print axioms memNextPlaced
#print axioms memFetch
#print axioms memV_Ldrb
#print axioms memV_Strb
#print axioms memV_Stp
#print axioms memV_Ldp
#print axioms memV_Stp8
#print axioms memV_Ldp8
end HeapV2StepCerts.MemNext
