-- Memory classes Stp8/Ldp8 support: the SDK split-pair skeleton premises
-- (MemPair8R.TAS / MemWriteD7.StrongTA) discharged from the canonical invariant under the
-- decision-171 no-update route, including at the state after the first 8-byte store
-- (CurrentS1At via current_s1_program_write; RawImageAt by separation).
import ArmCertWalk.DataNoUpdate
import ArmCertTranslateModel.CurrentProgramTransport
import MemM1.MemPair8R
import MemM1.MemPair8W
import MemM1.MemWriteD7
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem raw_image_program_write {rows : List ImageRow} {m m' : Mem} (raw : RawImageAt rows m)
    (writes : Nat → Prop) (frame : WritesOnly writes (fun a => m[a]?) (fun a => m'[a]?))
    (sep : Separated (rowsFootprint rows).byte writes) : RawImageAt rows m' := by
  intro row member i hi
  have inFp : (rowsFootprint rows).byte (row.slot + i) :=
    ⟨row.slot, List.mem_map.mpr ⟨row, member, rfl⟩, by omega, by simp only [rowsFootprint]; omega⟩
  have same := frame _ (sep _ inFp)
  simp only at same
  rw [same]
  exact raw row member i hi

/-- 8-byte store window footprint. -/
theorem wfold8_footprint {rows : List ImageRow} (mem : Mem) (pa : BitVec 56) (g : Nat → BitVec 8)
    (outside : ∀ i < 8, ¬ (rowsFootprint rows).byte (pa.toNat + i)) :
    WritesOnly (fun x => pa.toNat ≤ x ∧ x < pa.toNat + 8) (fun x => mem[x]?)
      (fun x => (MemM1.MemWriteD1.wfold mem pa.toNat 8 g)[x]?) ∧
    Separated (rowsFootprint rows).byte (fun x => pa.toNat ≤ x ∧ x < pa.toNat + 8) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [MemM1.MemWriteD1.wfold_get, hx, ↓reduceIte]
  · intro x table ⟨lo, hi⟩
    have := outside (x - pa.toNat) (by omega)
    rw [show pa.toNat + (x - pa.toNat) = x by omega] at this
    exact this table

/-- TAS (8-byte half, read) from the canonical invariant. -/
theorem tas_of_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (b : BitVec 64) (acc : AccessDescriptor)
    (member : domain ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (notFetch : (acc.acctype == .AccessType_IFETCH) = false) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping b = some pa.toNat) (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true) :
    MemM1.MemPair8R.TAS b acc pa s := by
  intro u ur um
  obtain ⟨ad, t1, call, f, p, n, i, o, v, r, m, _⟩ := translate_noupdate_at spec config rows mapping
    ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ member data s u ur um current access mode aa64 debug spe notFetch dcache
    pa mapped raw noUpd
  exact ⟨ad, t1, call, f, by rw [p], n, i, o, v, r.trans ur.symm, m.trans um.symm⟩

/-- StrongTA (8-byte half, write) from the canonical invariant. -/
theorem strongTA_of_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (b : BitVec 64) (acc : AccessDescriptor)
    (member : domain ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩)
    (data : S1AccessData spec config rows ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩)
    (current : CurrentS1At spec config rows s)
    (access : CurrentS1AccessAt spec config rows mapping ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ data s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (notFetch : (acc.acctype == .AccessType_IFETCH) = false) (dcache : currentDCache s.regs = true)
    (pa : BitVec 56) (mapped : mapping b = some pa.toNat) (raw : RawImageAt spec.imageRows s.mem)
    (noUpd : NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true) :
    MemM1.MemWriteD7.StrongTA b acc 8 pa s := by
  intro u ur um
  obtain ⟨ad, t1, call, f, p, n, _, _, v, r, m, _⟩ := translate_noupdate_at spec config rows mapping
    ⟨b, ⟨acc, true⟩, ((8 : Nat) : Int)⟩ member data s u ur um current access mode aa64 debug spe notFetch dcache
    pa mapped raw noUpd
  exact ⟨ad, t1, call, f, p, n, v, r.trans ur.symm, m.trans um.symm⟩

/-- CurrentS1At and RawImageAt after an 8-byte data store outside the tables (same registers). -/
theorem current_after_store8 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {s s1 : State}
    (current : CurrentS1At spec config rows s) (raw : RawImageAt spec.imageRows s.mem)
    (pa : BitVec 56) (g : Nat → BitVec 8)
    (outside : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i))
    (hr : s1.regs = s.regs) (hm : s1.mem = MemM1.MemWriteD1.wfold s.mem pa.toNat 8 g) :
    CurrentS1At spec config rows s1 ∧ RawImageAt spec.imageRows s1.mem := by
  obtain ⟨frame, sep⟩ := wfold8_footprint (rows := spec.imageRows) s.mem pa g outside
  have frame' : WritesOnly (fun x => pa.toNat ≤ x ∧ x < pa.toNat + 8) (fun x => s.mem[x]?) (fun x => s1.mem[x]?) := by
    rw [hm]; exact frame
  refine ⟨current_s1_program_write current _ frame' sep ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    raw_image_program_write raw _ frame' sep⟩ <;> (try intro _) <;> rw [hr]

#print axioms raw_image_program_write
#print axioms tas_of_current
#print axioms strongTA_of_current
#print axioms current_after_store8
end ArmCertWalk
