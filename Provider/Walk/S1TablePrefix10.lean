import Walk.S1NextTable10Facts
import Walk.S1EntryFrame
import Walk.S2OAFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1TablePrefix10
open S1Normality

def address (next : TTWState) (va : BitVec 64) : FullAddress :=
  S2NextEntryFrame.address next.level va next.baseaddress
def outOfRange (wp : S1TTWParams) (addr : FullAddress) : Bool :=
  !is_zero_subrange addr.address 55 (S2PhysicalSizeFrame.value wp.ps)

structure Certificate (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State) where
  next : TTWState
  afterNext : State
  afterAddress : State
  state : State
  next_eq : AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL10 wp d s =
    .ok next afterNext
  address_eq : AArch64_TTEntryAddress next.level 0#1 0#2 .TGx_4KB wp.txsz va
    next.baseaddress afterNext = .ok (address next va) afterAddress
  range_eq : AArch64_OAOutOfRange (address next va).address 0#1 wp.ps .TGx_4KB
    afterAddress = .ok (outOfRange wp (address next va)) state
  shape : S1NextTable10Facts.Shape current d next
  frame : Frame s state

theorem total (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hLevel : 0 ≤ current.level ∧ current.level ≤ 2)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48) :
    Nonempty (Certificate wp current d va s2fs1mro s) := by
  rcases S1NextTable10Facts.total current s2fs1mro wp d s hD128 hDS hTG hPAS with
    ⟨next, t1, hn, ⟨hr1, hm1, he1⟩, hshape⟩
  have hl : next.level = current.level + 1 := hshape.2.1
  have hNext : 0 ≤ next.level ∧ next.level ≤ 3 := by omega
  rcases S1EntryFrame.total next.level 0#2 wp.txsz va next.baseaddress t1 hNext with
    ⟨t2, ha, hr2, hm2, he2⟩
  have hPA2 : t2.regs.bank_Int .__supported_pa_size = 48 := by
    rw [hr2, hr1]
    exact hPA
  rcases S2OAFrame.total (address next va).address wp.ps t2 hPA2 with
    ⟨t3, ho, hr3, hm3, he3⟩
  exact ⟨{
    next := next
    afterNext := t1
    afterAddress := t2
    state := t3
    next_eq := hn
    address_eq := ha
    range_eq := ho
    shape := hshape
    frame := ⟨hr3.trans (hr2.trans hr1), hm3.trans (hm2.trans hm1), he3.trans (he2.trans he1)⟩
  }⟩
#print axioms total
end S1TablePrefix10
