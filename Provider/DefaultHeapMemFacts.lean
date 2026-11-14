-- Heap body memory geometry and real MTE2 tails, using current checked controls.
import DefaultHeapEntryMem
import HeapDefaultTagCheck.MemTailEffects

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.HeapV2Compose
open HeapV2StepCerts HeapV2StepCerts.MemFactsE HeapV2StepCerts.RegBind HeapV2StepCerts.C3
open NativeMteTagCheck
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapMemFacts

abbrev CurrentCtx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (p : HeapV2E17.Pins) (base : Nat) (table : Nat → Prop) (k : Nat)
    (catalogue : ControlCatalogue) (cost : Nat) : NativeState → Prop :=
  DefaultHeapEntryMem.FetchedCtxMte spec config rows mapping (HeapV2E17.consumerMap p base mapping table) p k catalogue cost

theorem prem_Strb {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (Rn : BitVec 5) (hat : accessAt e.1 = some (.x (rk Rn), 0)) (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = true) :
    (∀ acc, DataShape true acc → domain (MemClass.Strb.query fetched Rn acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Strb.query fetched Rn acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Strb.query fetched Rn acc) data fetched)) ∧
    ∃ pa : BitVec 56, mapping (MemClass.Strb.base fetched Rn) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ¬ (rowsFootprint spec.imageRows).byte pa.toNat := by
  have hva : MemClass.Strb.base fetched Rn = HeapV2E17.dataVA p e := base_va member bound hat
  obtain ⟨pa, facts⟩ := data_facts static member
  refine ⟨fun acc shape => ?_, pa, by rw [hva]; exact facts.mapped, facts.mmio,
    by have := facts.outside 0 (by omega); simpa using this⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact r

theorem prem_Stp {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (imm7 : BitVec 7) {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0) (hc : e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) :
    (∀ acc, DataShape true acc → domain (MemClass.Stp.query fetched imm7 acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Stp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query fetched imm7 acc) data fetched)) ∧
    fetched.regs.SP_EL0.toNat % 16 = 0 ∧ (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0 ∧
    ∃ pa : BitVec 56, mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
      ∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i) := by
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member bound hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  have hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0 := by rw [hva]; exact dataVA_aligned pinAligned hc
  have hsp : fetched.regs.SP_EL0.toNat % 16 = 0 :=
    add_aligned _ off (by have := hal; simp only [ArmCertMem.LdpEval.ldpAddr, himm] at this; exact this) hoff
  obtain ⟨pa, facts⟩ := data_facts static member
  refine ⟨fun acc shape => ?_, hsp, hal, pa, by rw [hva]; exact facts.mapped, facts.mmio,
    fun i hi => facts.outside i (by omega)⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact r

theorem prem_Stp8 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop} (fetched : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap p base mapping table) fetched)
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (bound : RegBind p e.1 fetched)
    (Rn : BitVec 5) (imm7 : BitVec 7) {off : Int} (hat : accessAt e.1 = some (.x (rk Rn), off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hc : e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) :
    (∀ acc, DataShape true acc → PairAccess spec config rows mapping (MemClass.Stp8.pairAddr fetched Rn imm7) acc fetched) ∧
    (MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 8 = 0 ∧
    ∃ pa1 pa2 : BitVec 56, mapping (MemClass.Stp8.pairAddr fetched Rn imm7) = some pa1.toNat ∧
      mapping (plus8 (MemClass.Stp8.pairAddr fetched Rn imm7)) = some pa2.toNat ∧
      ((MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8) ∧
      MemM1.MemReadIF.NotMMIO pa1 ∧ MemM1.MemReadIF.NotMMIO pa2 ∧
      (∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i)) ∧
      (∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa2.toNat + i)) := by
  have hva : MemClass.Stp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e := pair8_va member bound Rn imm7 hat himm
  have hal : (MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 16 = 0 := by rw [hva]; exact dataVA_aligned pinAligned hc
  obtain ⟨pa, facts⟩ := data_facts static member
  have h2 := pa2_toNat pa _ facts.bound hsize
  obtain ⟨up, upm⟩ := facts.upper hsize
  refine ⟨fun acc shape => ⟨fun _ => ?_, fun h => absurd hal h⟩,
    by omega, pa, BitVec.ofNat 56 (pa.toNat + 8), by rw [hva]; exact facts.mapped,
    by rw [hva, h2]; exact up, fun _ => h2, facts.mmio, upm _ (by rw [hva, h2] at *; exact up),
    fun i hi => facts.outside i (by omega), fun i hi => by rw [h2, Nat.add_assoc]; exact facts.outside (8 + i) (by omega)⟩
  have r := access_of_closed closed member hva (hw ▸ shape)
  rw [hsize] at r
  exact r

#check "CURRENT_DECL memE_Ldrb"
theorem memE_Ldrb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    {r : Reg} (hat : accessAt e.1 = some (r, 0)) (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdrb Rn Rt imm9) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 1) (fun _ => False)
      (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) NativeEntryBodyMem.Ldrb.writes 631 source
      (source.regs._PC + 4#64) (upds k) (fun _ _ => True)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hvaE : MemClass.Ldrb.base fetched Rn = HeapV2E17.dataVA p e := base_va member ctx.regBind hat
  obtain ⟨perAcc, pa, mapped, mmio, outside, v, byte⟩ :=
    prem_Ldrb fetched ctx.closed static ctx.present member ctx.regBind Rn hat hsize hw
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inD⟩, choice, bound⟩ :=
    MemTailE.mem_tailDefault236_Ldrb real spec config rows mapping source fetched enc0 imm9 Rn Rt hRn hRt hRnt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.dcache pa mapped mmio v byte outside (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inD, gic, pc, np, keep, holds, trivial, ⟨delta, ev, fun nd => by rw [(recs nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩

#check "CURRENT_DECL memE_Strb"
theorem memE_Strb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows))
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Strb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    {r : Reg} (hat : accessAt e.1 = some (r, 0)) (hr : r = .x (rk Rn))
    (hsize : e.2.2.2.1 = 1) (hw : e.2.2.2.2 = true) (hupd : upds k = updStrb Rn imm9) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 1) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Strb.selected Rt Rn imm9) NativeEntryBodyMem.Strb.writes 649 source
      (source.regs._PC + 4#64) (upds k) (fun _ _ => True)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hvaE : MemClass.Strb.base fetched Rn = HeapV2E17.dataVA p e := base_va member ctx.regBind hat
  have hva := base_va member ctx.regBind hat
  obtain ⟨perAcc, pa, mapped, mmio, outside⟩ :=
    prem_Strb fetched ctx.closed static member ctx.regBind Rn hat hsize hw
  have inD : RtSaved.accPA p mapping e pa.toNat :=
    Or.inl ⟨pa.toNat, hva ▸ mapped, Nat.le_refl _, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW⟩, choice, bound⟩ :=
    MemTailE.mem_tailDefault236_Strb real spec config rows mapping source fetched enc0 imm9 Rn Rt hRn hRt hRnt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.dcache pa mapped mmio outside (RtSaved.accPA p mapping e) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, trivial, ⟨delta, ev, fun nd => by rw [(recs nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩

#check "CURRENT_DECL memE_Stp"
theorem memE_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 1) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) NativeEntryBodyMem.Stp.writes 617 source
      (source.regs._PC + 4#64) (upds k) (fun _ _ => True)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hvaE : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  have hva : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    prem_Stp fetched ctx.closed static pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  have inD : ∀ i < 16, RtSaved.accPA p mapping e (pa.toNat + i) := fun i hi =>
    Or.inl ⟨pa.toNat, hva ▸ mapped, by omega, by rw [hsize]; omega⟩
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW⟩, choice, bound⟩ :=
    MemTailE.mem_tailDefault236_Stp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio outside (RtSaved.accPA p mapping e) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, trivial, ⟨delta, ev, fun nd => by rw [(recs nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩

#check "CURRENT_DECL memE_Ldp"
theorem memE_Ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : DataStatic p mapping (rowsFootprint spec.imageRows)) (pinAligned : ∀ i, HeapV2E17.pin p i % 16 = 0)
    {k : Nat} {e : Nat × Nat × Int × Nat × Bool} (member : e ∈ HeapV2Plan.symbolicAccesses) (hk : e.1 = k)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    {off : Int} (hat : accessAt e.1 = some (.sp, off))
    (himm : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 off) (hoff : off % 16 = 0 ∧ e.2.2.1 % 16 = 0)
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 1) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) NativeEntryBodyMem.Ldp.writes 611 source
      (source.regs._PC + 4#64) (upds k) (fun _ _ => True)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 1 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk
  rw [hupd]
  have hvaE : ArmCertMem.LdpEval.ldpAddr fetched imm7 = HeapV2E17.dataVA p e := by
    have h := va_of_bind member ctx.regBind hat
    simp only [regVal] at h
    simp only [ArmCertMem.LdpEval.ldpAddr, himm, h]
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    prem_Ldp fetched ctx.closed static ctx.present pinAligned member ctx.regBind imm7 hat himm hoff.1 hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW⟩, choice, bound⟩ :=
    MemTailE.mem_tailDefault236_Ldp real spec config rows mapping source fetched enc0 imm7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (fun _ => False) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, trivial, ⟨delta, ev, fun nd => by rw [(recs nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩

#check "CURRENT_DECL memE_Stp8"
theorem memE_Stp8 (real : Type) [Sail.SailReal real]
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
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = true) (hupd : upds k = []) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 2) (RtSaved.accPA p mapping e)
      (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) NativeEntryBodyMem.Stp8.writes 617 source
      (source.regs._PC + 4#64) (upds k) (fun _ _ => True)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 2 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hvaE : MemClass.Stp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e := pair8_va member ctx.regBind Rn imm7 hat himm
  have hva : MemClass.Stp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e :=
    pair8_va member ctx.regBind Rn imm7 hat himm
  obtain ⟨perAcc, h8, pa1, pa2, mapped1, mapped2, contiguous, mmio1, mmio2, outside1, outside2⟩ :=
    prem_Stp8 fetched ctx.closed static pinAligned member ctx.regBind Rn imm7 hat himm hoff.2 hsize hw
  have inD1 : ∀ i < 8, RtSaved.accPA p mapping e (pa1.toNat + i) := fun i hi =>
    Or.inl ⟨pa1.toNat, hva ▸ mapped1, by omega, by rw [hsize]; omega⟩
  have inD2 : ∀ i < 8, RtSaved.accPA p mapping e (pa2.toNat + i) := fun i hi =>
    Or.inr ⟨hsize, pa2.toNat, hva ▸ mapped2, by omega, by omega⟩
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW⟩, choice, bound⟩ :=
    MemTailE.mem_tailDefault236_Stp8 real spec config rows mapping source fetched enc0 imm7 Rn Rt Rt2 hRn hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache h8 pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 outside1 outside2
      (RtSaved.accPA p mapping e) inD1 inD2 ctx.raw (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, trivial, ⟨delta, ev, fun nd => by rw [(recs (by rw [hvaE]; exact dataVA_aligned pinAligned hoff.2) nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩

#check "CURRENT_DECL memE_Ldp8"
theorem memE_Ldp8 (real : Type) [Sail.SailReal real]
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
    (hsize : e.2.2.2.1 = 16) (hw : e.2.2.2.2 = false) (hupd : upds k = updLdp Rt Rt2) (catalogue : ControlCatalogue) (source : NativeState) :
    DefaultHeapEntryMem.MemTailDefaultAt real spec config rows (CurrentCtx spec config rows mapping p base table k catalogue 2) (fun _ => False)
      (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) NativeEntryBodyMem.Ldp8.writes 611 source
      (source.regs._PC + 4#64) (upds k) (fun _ _ => True)
      (DataRecs.dataRecs spec (HeapV2E17.dataVA p e) e.2.2.2.2 e.2.2.2.1) 2 := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  subst hk hr
  rw [hupd]
  have hvaE : MemClass.Ldp8.pairAddr fetched Rn imm7 = HeapV2E17.dataVA p e := pair8_va member ctx.regBind Rn imm7 hat himm
  obtain ⟨perAcc, h8, pa1, pa2, mapped1, mapped2, contiguous, mmio1, mmio2, data, bytes1, bytes2⟩ :=
    prem_Ldp8 fetched ctx.closed static ctx.present pinAligned member ctx.regBind Rn imm7 hat himm hoff.2 hsize hw
  obtain ⟨sp, a, fin, written, delta, draws, hook, run, frame, q, fp, sys, wo, sep, ev, _, recs, flg, gic, pc, np, keep, ⟨holds, inW⟩, choice, bound⟩ :=
    MemTailE.mem_tailDefault236_Ldp8 real spec config rows mapping source fetched enc0 imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post catalogue ctx.controls ctx.statusRows ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache h8 pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 data bytes1 bytes2
      (fun _ => False) ctx.raw (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds, trivial, ⟨delta, ev, fun nd => by rw [(recs (by rw [hvaE]; exact dataVA_aligned pinAligned hoff.2) nd), hvaE, hw, hsize]⟩, ValueTailE.z_tail quiet hook frame rfl np, flg, draws, choice, bound⟩


#print axioms memE_Ldrb
#print axioms memE_Strb
#print axioms memE_Stp
#print axioms memE_Ldp
#print axioms memE_Stp8
#print axioms memE_Ldp8
end ReleaseProfile.DefaultHeapMemFacts
