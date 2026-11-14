-- Route 7 positive-C2 world (loops): entry RAM plan, entry data and code statics over Route7GB10.World.
-- Code: memory.elf's 43 reviewed RX words (ArmCertLoop.ContractDraft.image, 0x1a4..0x250) at PA 0x80100000 + offset
-- behind VA page 0x400000; tables as generated; data: one source byte at s = 0x30000 (PA 0x80600000) and the
-- destination byte at d = 0x31000 (PA 0x80601000). Program data only: every register outside DataPart is the canonical
-- source (makeModelEntry).
import Route7GB10.World
import ArmCertLoop.ContractDraft
import ArmCertTranslateModel.PlanChecks
import ReleaseProfile.GB10.ModelEntry
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Route7GB10.Plan
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmCertLoop ReleaseProfile.GB10

def B : BitVec 64 := 0x400000#64
def codePA : Nat := 0x80100000
def codeLen : Nat := 4 * Generated.imageWords.length

def codePlan : NativeSourceInit.Plan := (List.range codeLen).map fun j =>
  (codePA + Generated.imageStart + j, (ContractDraft.image (Generated.imageStart + j)).getD 0)
def tableRows : NativeSourceInit.Plan := imageRowsPlan Route7GB10.World.imageRows
def srcByte : BitVec 8 := 0x5a#8
def dataPlan : NativeSourceInit.Plan := [(0x80600000, srcByte), (0x80601000, 0#8)]
def plan : NativeSourceInit.Plan := codePlan ++ tableRows ++ dataPlan

theorem plan_nodup : (plan.map (·.1)).Nodup := by decide +kernel

theorem planKeys : plan.Pairwise (fun a b => (a.1 == b.1) = false) := by
  have h := List.pairwise_map.1 (List.nodup_iff_pairwise_ne.1 plan_nodup)
  exact h.imp fun {a b} ne => by simpa [beq_eq_false_iff_ne] using ne

/-- Entry data: GPRs, SP_EL0 = 0x200000 (unused), PC = B + entry, page-table roots at the world root. -/
def entryData (gprs : Vector (BitVec 64) 31) (entry : Nat) : DataPart where
  gpr := gprs
  SP_EL3 := 0#64
  SP_EL2 := 0#64
  SP_EL1 := 0#64
  SP_EL0 := 0x200000#64
  _ZT0 := 0#512
  _ZA := Vector.replicate 256 0#2048
  _FFR := 0#256
  _P := Vector.replicate 16 0#256
  _Z := Vector.replicate 32 0#2048
  PhysicalCount := 0#88
  _PC := B + BitVec.ofNat 64 entry
  TTBR0_EL2 := 0x80000000#128
  TTBR1_EL2 := 0#128
  HTTBR := 0x80000000#64
  timers := fun _ => 0#64

def payload (gprs : Vector (BitVec 64) 31) (entry : Nat) (pcount : BitVec 88) : ModelPayload :=
  ⟨{ entryData gprs entry with PhysicalCount := pcount }, Std.ExtHashMap.ofList plan⟩

theorem timers_disabled (gprs : Vector (BitVec 64) 31) (entry : Nat) (pcount : BitVec 88) :
    TimersDisabled (payload gprs entry pcount).data.timers := fun _ _ => by simp [payload, entryData]

theorem realizes (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (gprs : Vector (BitVec 64) 31) (entry : Nat) (pcount : BitVec 88) :
    NativeSourceInit.Satisfies plan (makeModelEntry sem rho caller (payload gprs entry pcount)).mem :=
  fun ⟨_, _⟩ mem => Std.ExtHashMap.getElem?_ofList_of_mem (BEq.refl _) planKeys mem

/-! ## Code statics (kernel sweeps over the 172 reviewed code bytes) -/

def codeByteOK (off : Nat) : Bool :=
  (ContractDraft.image off).isSome &&
  decide (Route7GB10.World.mapping (MemReloc.imageAddress B off) = some (codePA + off)) &&
  plan.contains (codePA + off, (ContractDraft.image off).getD 0) &&
  decide (Sail.BitVec.extractLsb (BitVec.ofNat 56 (codePA + off)) 55 16 ≠ 0x2C00#40) &&
  decide (Sail.BitVec.extractLsb (BitVec.ofNat 56 (codePA + off)) 55 16 ≠ 0x3C00#40) &&
  decide (codePA + off < 2 ^ 56) && decide (codePA + off ≥ 0x80005000)

theorem code_ok : (List.range codeLen).all (fun j => codeByteOK (Generated.imageStart + j)) = true := by decide +kernel

theorem code_at (off : Nat) (h : ContractDraft.codeScope off) : codeByteOK off = true := by
  have := List.all_eq_true.1 code_ok (off - Generated.imageStart)
    (List.mem_range.2 (by unfold ContractDraft.codeScope codeLen at *; omega))
  rwa [show Generated.imageStart + (off - Generated.imageStart) = off by unfold ContractDraft.codeScope at h; omega] at this

theorem code_map (off : Nat) (h : ContractDraft.codeScope off) :
    Route7GB10.World.mapping (MemReloc.imageAddress B off) = some (codePA + off) := by
  have ok := code_at off h
  simp only [codeByteOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ok.1.1.1.1.1.2

theorem placedAt (x : ArmBridge.Draft.NativeState) (hm : NativeSourceInit.Satisfies plan x.mem) :
    MemReloc.ImageOn ContractDraft.codeScope ContractDraft.image x B Route7GB10.World.mapping := by
  intro off h
  have ok := code_at off h
  simp only [codeByteOK, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at ok
  obtain ⟨⟨⟨⟨⟨⟨some_, map⟩, mem⟩, _⟩, _⟩, _⟩, _⟩ := ok
  obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.1 some_
  refine ⟨byte, codePA + off, hb, map, ?_⟩
  have := hm _ mem
  simpa [hb] using this

/-- World table slots lie below 0x80005000. -/
theorem slots_range : Route7GB10.World.imageRows.all (fun r => decide (r.slot + 8 ≤ 0x80005000)) = true := by
  decide +kernel

theorem separatedAt : ImageTableSeparated ContractDraft.codeScope B Route7GB10.World.mapping
    (rowsFootprint Route7GB10.World.imageRows).byte := by
  intro off pa inside hmap ⟨slot, hs, lo, hi⟩
  have ok := code_at off inside
  simp only [codeByteOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  rw [ok.1.1.1.1.1.2] at hmap
  cases hmap
  simp only [rowsFootprint, List.mem_map] at hs
  obtain ⟨row, rm, rfl⟩ := hs
  have hs := of_decide_eq_true (List.all_eq_true.1 slots_range row rm)
  have hw : (rowsFootprint Route7GB10.World.imageRows).width = 8 := rfl
  have far := ok.2
  omega

theorem codeGeometry : ContractDraft.CodeGeometry Route7GB10.World.mapping B := by
  intro i hi
  have inScope : ∀ k, k < 4 → ContractDraft.codeScope (Generated.imageStart + 4 * i + k) := by
    intro k hk; unfold ContractDraft.codeScope; omega
  refine ⟨?_, ?_⟩
  · intro k hk pa hpa
    rw [code_map _ (by simpa using inScope 0 (by omega))] at hpa
    cases hpa
    rw [code_map _ (inScope k hk)]
    congr 1; omega
  · intro pa hpa
    have ok := code_at _ (by simpa using inScope 0 (by omega))
    simp only [codeByteOK, Bool.and_eq_true, decide_eq_true_eq] at ok
    rw [ok.1.1.1.1.1.2] at hpa
    have e : pa = BitVec.ofNat 56 (codePA + (Generated.imageStart + 4 * i)) := by
      apply BitVec.eq_of_toNat_eq; rw [← Option.some.inj hpa, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt ok.1.2).symm
    rw [e]; exact ⟨ok.1.1.1.2, ok.1.1.2⟩

end Route7GB10.Plan
#print axioms Route7GB10.Plan.placedAt
#print axioms Route7GB10.Plan.separatedAt
#print axioms Route7GB10.Plan.codeGeometry
