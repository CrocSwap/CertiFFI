import Pilot.S1NextTableFacts
import Walk.S2NextEntryFrame
import Walk.S2OAFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1TablePrefix
abbrev State := SequentialState Regs oracleChoiceSource
def address (next : TTWState) (va : BitVec 64) : FullAddress :=
  S2NextEntryFrame.address next.level va next.baseaddress
def outOfRange (wp : S1TTWParams) (addr : FullAddress) : Bool :=
  !is_zero_subrange addr.address 55 (S2PhysicalSizeFrame.value wp.ps)

/- Constructed from actual callee theorems; this certificate is not a premise
   requiring callers to assume successful source execution. -/
structure Certificate (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State) where
  next : TTWState
  afterNext : State
  afterAddress : State
  state : State
  next_eq : AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL20 wp d s =
    .ok next afterNext
  address_eq : AArch64_TTEntryAddress next.level 0#1 0#2 .TGx_4KB wp.txsz va
    next.baseaddress afterNext = .ok (address next va) afterAddress
  range_eq : AArch64_OAOutOfRange (address next va).address 0#1 wp.ps .TGx_4KB
    afterAddress = .ok (outOfRange wp (address next va)) state
  level_eq : next.level = current.level + 1
  regs_eq : state.regs = s.regs
  mem_eq : state.mem = s.mem

theorem total (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hLevel : 0 ≤ current.level ∧ current.level ≤ 2)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48) :
    Nonempty (Certificate wp current d va s2fs1mro s) := by
  rcases S1NextTableFacts.model_returns current s2fs1mro wp d s hD128 hDS hTG with
    ⟨next, t1, hn, hl⟩
  have hf := S1NextTableFacts.native_frame current s2fs1mro wp d s
  rw [← S1NextTable.complete current s2fs1mro wp d s hD128 hDS hTG, hn] at hf
  change t1.regs = s.regs ∧ t1.mem = s.mem at hf
  have hNext : 0 ≤ next.level ∧ next.level ≤ 3 := by omega
  rcases S2NextEntryFrame.total next.level 0#2 wp.txsz va next.baseaddress t1 hNext with
    ⟨t2, he, hr2, hm2⟩
  have hPA2 : t2.regs.bank_Int .__supported_pa_size = 48 := by
    rw [hr2, hf.1]
    exact hPA
  rcases S2OAFrame.total (address next va).address wp.ps t2 hPA2 with
    ⟨t3, ho, hr3, hm3, _⟩
  exact ⟨{
    next := next
    afterNext := t1
    afterAddress := t2
    state := t3
    next_eq := hn
    address_eq := he
    range_eq := ho
    level_eq := hl
    regs_eq := hr3.trans (hr2.trans hf.1)
    mem_eq := hm3.trans (hm2.trans hf.2)
  }⟩
#print axioms total
end S1TablePrefix
