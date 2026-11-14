import NativeEntryDispatch.MrsDitWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace NativeEntryDispatch.MrsDit
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 5 0) : BitVec 6) = 31#6) := by
  revert Rt
  decide +kernel

theorem dispatch_h0b (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 5 0) : BitVec 6) == 31#6) = false := by
  revert Rt
  decide +kernel

theorem dispatch_h1 (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 7 0) : BitVec 8) = 95#8) := by
  revert Rt
  decide +kernel

theorem dispatch_h1b (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 7 0) : BitVec 8) == 95#8) = false := by
  revert Rt
  decide +kernel

theorem dispatch_h2 (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 7 0) : BitVec 8) = 159#8) := by
  revert Rt
  decide +kernel

theorem dispatch_h2b (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 7 0) : BitVec 8) == 159#8) = false := by
  revert Rt
  decide +kernel

theorem dispatch_h3 (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 7 0) : BitVec 8) = 223#8) := by
  revert Rt
  decide +kernel

theorem dispatch_h3b (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 7 0) : BitVec 8) == 223#8) = false := by
  revert Rt
  decide +kernel

theorem dispatch_h4 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 8 6) : BitVec 3) = 2#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h5 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 8 6) : BitVec 3) = 2#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h6 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 8 6) : BitVec 3) = 2#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h7 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 8 6) : BitVec 3) = 2#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h8 (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 9 0) : BitVec 10) = 575#10) := by
  revert Rt
  decide +kernel

theorem dispatch_h8b (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 9 0) : BitVec 10) == 575#10) = false := by
  revert Rt
  decide +kernel

theorem dispatch_h9 (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 9 0) : BitVec 10) = 1023#10) := by
  revert Rt
  decide +kernel

theorem dispatch_h9b (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 9 0) : BitVec 10) == 1023#10) = false := by
  revert Rt
  decide +kernel

theorem dispatch_h10 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 15 12) : BitVec 4) = 4#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h11 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 23 11) : BitVec 13) = 1896#13 := by
  revert Rt
  decide +kernel

theorem dispatch_h12 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 23 11) : BitVec 13) = 1896#13 := by
  revert Rt
  decide +kernel

theorem dispatch_h13 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 25 25) : BitVec 1) = 0#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h14 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 27 25) : BitVec 3) = 2#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h15 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 27 27) : BitVec 1) = 0#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h16 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 28 25) : BitVec 4) = 10#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h17 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 28 25) : BitVec 4) = 10#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h18 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 28 25) : BitVec 4) = 10#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h19 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 28 25) : BitVec 4) = 10#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h20 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 28 26) : BitVec 3) = 5#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h21 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 28 26) : BitVec 3) = 5#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h22 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 30 24) : BitVec 7) = 85#7 := by
  revert Rt
  decide +kernel

theorem dispatch_h23 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 30 24) : BitVec 7) = 85#7 := by
  revert Rt
  decide +kernel

theorem dispatch_h24 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 30 24) : BitVec 7) = 85#7 := by
  revert Rt
  decide +kernel

theorem dispatch_h25 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 30 24) : BitVec 7) = 85#7 := by
  revert Rt
  decide +kernel

theorem dispatch_h26 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 5) : BitVec 27) = 111794709#27 := by
  revert Rt
  decide +kernel

theorem dispatch_h27 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 5) : BitVec 27) = 111794709#27 := by
  revert Rt
  decide +kernel

theorem dispatch_h28 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 5) : BitVec 27) = 111794709#27 := by
  revert Rt
  decide +kernel

theorem dispatch_h29 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 5) : BitVec 27) = 111794709#27 := by
  revert Rt
  decide +kernel

theorem dispatch_h30 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 8) : BitVec 24) = 13974338#24 := by
  revert Rt
  decide +kernel

theorem dispatch_h31 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 10) : BitVec 22) = 3493584#22 := by
  revert Rt
  decide +kernel

theorem dispatch_h32 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 10) : BitVec 22) = 3493584#22 := by
  revert Rt
  decide +kernel

theorem dispatch_h33 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 10) : BitVec 22) = 3493584#22 := by
  revert Rt
  decide +kernel

theorem dispatch_h34 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 10) : BitVec 22) = 3493584#22 := by
  revert Rt
  decide +kernel

theorem dispatch_h35 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 11) : BitVec 21) = 1746792#21 := by
  revert Rt
  decide +kernel

theorem dispatch_h36 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 11) : BitVec 21) = 1746792#21 := by
  revert Rt
  decide +kernel

theorem dispatch_h37 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 12) : BitVec 20) = 873396#20 := by
  revert Rt
  decide +kernel

theorem dispatch_h38 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 12) : BitVec 20) = 873396#20 := by
  revert Rt
  decide +kernel

theorem dispatch_h39 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 19) : BitVec 13) = 6823#13 := by
  revert Rt
  decide +kernel

theorem dispatch_h40 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 19) : BitVec 13) = 6823#13 := by
  revert Rt
  decide +kernel

theorem dispatch_h41 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 19) : BitVec 13) = 6823#13 := by
  revert Rt
  decide +kernel

theorem dispatch_h42 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 19) : BitVec 13) = 6823#13 := by
  revert Rt
  decide +kernel

theorem dispatch_h43 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 20) : BitVec 12) = 3411#12 := by
  revert Rt
  decide +kernel

theorem dispatch_h44 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 20) : BitVec 12) = 3411#12 := by
  revert Rt
  decide +kernel

theorem dispatch_h45 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 20) : BitVec 12) = 3411#12 := by
  revert Rt
  decide +kernel

theorem dispatch_h46 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 20) : BitVec 12) = 3411#12 := by
  revert Rt
  decide +kernel

theorem dispatch_h47 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 21) : BitVec 11) = 1705#11 := by
  revert Rt
  decide +kernel

theorem dispatch_h48 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 21) : BitVec 11) = 1705#11 := by
  revert Rt
  decide +kernel

theorem dispatch_h49 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 21) : BitVec 11) = 1705#11 := by
  revert Rt
  decide +kernel

theorem dispatch_h50 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 21) : BitVec 11) = 1705#11 := by
  revert Rt
  decide +kernel

theorem dispatch_h51 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 21) : BitVec 11) = 1705#11 := by
  revert Rt
  decide +kernel

theorem dispatch_h52 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 24) : BitVec 8) = 213#8 := by
  revert Rt
  decide +kernel

theorem dispatch_h53 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 25) : BitVec 7) = 106#7 := by
  revert Rt
  decide +kernel

theorem dispatch_h54 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 26) : BitVec 6) = 53#6 := by
  revert Rt
  decide +kernel

theorem dispatch_h55 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 26) : BitVec 6) = 53#6 := by
  revert Rt
  decide +kernel

theorem dispatch_h56 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 31) : BitVec 1) = 1#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h57 (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.MrsDit.word Rt) 31 31) : BitVec 1) = 1#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h58 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 0 5 = Rt := by
  revert Rt
  decide +kernel

theorem dispatch_h59 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 5 2 = 1#2 := by
  revert Rt
  decide +kernel

theorem dispatch_h60 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 5 3 = 5#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h61 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 5 5 = 21#5 := by
  revert Rt
  decide +kernel

theorem dispatch_h62 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 5 14 = 6677#14 := by
  revert Rt
  decide +kernel

theorem dispatch_h63 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 5 16 = 55829#16 := by
  revert Rt
  decide +kernel

theorem dispatch_h64 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 5 19 = 121365#19 := by
  revert Rt
  decide +kernel

theorem dispatch_h65 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 8 4 = 2#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h66 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 10 1 = 0#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h67 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 10 2 = 0#2 := by
  revert Rt
  decide +kernel

theorem dispatch_h68 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 11 1 = 0#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h69 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 12 4 = 4#4 := by
  revert Rt
  decide +kernel

theorem dispatch_h70 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 16 3 = 3#3 := by
  revert Rt
  decide +kernel

theorem dispatch_h71 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 19 1 = 1#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h72 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 19 5 = 7#5 := by
  revert Rt
  decide +kernel

theorem dispatch_h73 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 21 1 = 1#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h74 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 21 2 = 1#2 := by
  revert Rt
  decide +kernel

theorem dispatch_h75 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 24 1 = 1#1 := by
  revert Rt
  decide +kernel

theorem dispatch_h76 (Rt : BitVec 5) :
    BitVec.slice (NativeEntryDispatch.MrsDit.word Rt) 31 1 = 1#1 := by
  revert Rt
  decide +kernel

theorem dispatch_hw77 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573563423#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw78 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573563455#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw79 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573563487#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw80 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573751839#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw81 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573751871#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw82 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573751903#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw83 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573751935#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw84 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573751967#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw85 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573751999#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw86 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752031#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw87 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752063#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw88 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752351#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw89 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752383#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw90 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752415#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw91 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752447#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw92 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752479#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw93 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573752543#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw94 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573753119#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw95 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573756031#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw96 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3573756159#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw97 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3600745440#32) := by
  revert Rt
  decide +kernel

theorem dispatch_hw98 (Rt : BitVec 5) :
    ¬ ((NativeEntryDispatch.MrsDit.word Rt) = 3602842592#32) := by
  revert Rt
  decide +kernel

theorem dispatch (pc : Int) (Rt : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryDispatch.MrsDit.word Rt) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 701))
      if c = true then (do writeReg Register.SEE 701; decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h2b, dispatch_h3, dispatch_h3b, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_hw77, dispatch_hw78, dispatch_hw79, dispatch_hw80, dispatch_hw81, dispatch_hw82, dispatch_hw83, dispatch_hw84, dispatch_hw85, dispatch_hw86, dispatch_hw87, dispatch_hw88, dispatch_hw89, dispatch_hw90, dispatch_hw91, dispatch_hw92, dispatch_hw93, dispatch_hw94, dispatch_hw95, dispatch_hw96, dispatch_hw97, dispatch_hw98, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_BranchExcSys
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h2b, dispatch_h3, dispatch_h3b, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_hw77, dispatch_hw78, dispatch_hw79, dispatch_hw80, dispatch_hw81, dispatch_hw82, dispatch_hw83, dispatch_hw84, dispatch_hw85, dispatch_hw86, dispatch_hw87, dispatch_hw88, dispatch_hw89, dispatch_hw90, dispatch_hw91, dispatch_hw92, dispatch_hw93, dispatch_hw94, dispatch_hw95, dispatch_hw96, dispatch_hw97, dispatch_hw98, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rt : BitVec 5) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 701) :
    (__DecodeA64 (real := real) pc (word Rt) : SailM Unit) s =
      (do writeReg Register.SEE 701; decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit) s := by
  rw [dispatch real pc Rt]
  have h : (s.regs.bank_Int .SEE <b 701) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 701)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 701) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryDispatch.MrsDit
