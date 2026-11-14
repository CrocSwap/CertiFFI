import GetEntry.InitialStateFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1InitialEntryAddress
abbrev State := S1Normality.State

def address (va : BitVec 64) (base : FullAddress) : FullAddress :=
  {paspace := base.paspace
   address := base.address |||
     (va.extractLsb' 39 9 +++ 0#3).setWidth 56}

theorem total (wp : S1TTWParams) (va : BitVec 64) (base : FullAddress) (s : State)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB) (htx : wp.txsz = 16#6) :
    ∃ t, AArch64_S1SLTTEntryAddress 0 wp va base s = .ok (address va base) t ∧
      S1Normality.Frame s t := by
  cases wp
  simp only [] at hd htg htx
  cases hd
  cases htg
  cases htx
  let n := s.choiceOcc.getD 1501 0
  let u : State := {s with choiceOcc := s.choiceOcc.insert 1501 (n + 1)}
  have ho : occLabel 1501 s = .ok (.occ 1501 n) u := rfl
  rcases S1Unknowns.undefined_full_address_total (.occ 1501 n) u with
    ⟨unused, t, hu, hr, hm, he⟩
  refine ⟨t, ?_, hr, hm, he⟩
  simp [AArch64_S1SLTTEntryAddress, address, AArch64_IASize, TGxGranuleBits,
    FINAL_LEVEL, ho, hu, ArmFull.assert, PreSail.assert,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
  rfl
#print axioms total
end S1InitialEntryAddress
