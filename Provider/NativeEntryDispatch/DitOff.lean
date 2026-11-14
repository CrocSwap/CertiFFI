import NativeEntryDispatch.DitOffWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace NativeEntryDispatch.DitOff
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0  :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 0) : BitVec 5) = 31#5 := by
  decide +kernel

theorem dispatch_h1  :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 0) : BitVec 5) = 31#5 := by
  decide +kernel

theorem dispatch_h2  :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 0) : BitVec 5) = 31#5 := by
  decide +kernel

theorem dispatch_h3  :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 0) : BitVec 5) = 31#5 := by
  decide +kernel

theorem dispatch_h4  :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 0) : BitVec 5) = 31#5 := by
  decide +kernel

theorem dispatch_h5  :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 4) : BitVec 1) = 1#1 := by
  decide +kernel

theorem dispatch_h6  :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 4 4) : BitVec 1) = 1#1 := by
  decide +kernel

theorem dispatch_h7  :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 5 0) : BitVec 6) = 31#6 := by
  decide +kernel

theorem dispatch_h8  :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 7 0) : BitVec 8) = 95#8 := by
  decide +kernel

theorem dispatch_h9  :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 7 0) : BitVec 8) = 95#8 := by
  decide +kernel

theorem dispatch_h10  :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 7 0) : BitVec 8) = 95#8 := by
  decide +kernel

theorem dispatch_h11  :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 7 0) : BitVec 8) = 95#8 := by
  decide +kernel

theorem dispatch_h12  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 8 6) : BitVec 3) = 1#3 := by
  decide +kernel

theorem dispatch_h13  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 8 6) : BitVec 3) = 1#3 := by
  decide +kernel

theorem dispatch_h14  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 8 6) : BitVec 3) = 1#3 := by
  decide +kernel

theorem dispatch_h15  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 8 6) : BitVec 3) = 1#3 := by
  decide +kernel

theorem dispatch_h16  :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 9 0) : BitVec 10) = 95#10 := by
  decide +kernel

theorem dispatch_h17  :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 9 0) : BitVec 10) = 95#10 := by
  decide +kernel

theorem dispatch_h18  :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 15 12) : BitVec 4) = 4#4 := by
  decide +kernel

theorem dispatch_h19  :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 23 11) : BitVec 13) = 104#13 := by
  decide +kernel

theorem dispatch_h20  :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 23 11) : BitVec 13) = 104#13 := by
  decide +kernel

theorem dispatch_h21  :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 25 25) : BitVec 1) = 0#1 := by
  decide +kernel

theorem dispatch_h22  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 27 25) : BitVec 3) = 2#3 := by
  decide +kernel

theorem dispatch_h23  :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 27 27) : BitVec 1) = 0#1 := by
  decide +kernel

theorem dispatch_h24  :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 28 25) : BitVec 4) = 10#4 := by
  decide +kernel

theorem dispatch_h25  :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 28 25) : BitVec 4) = 10#4 := by
  decide +kernel

theorem dispatch_h26  :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 28 25) : BitVec 4) = 10#4 := by
  decide +kernel

theorem dispatch_h27  :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 28 25) : BitVec 4) = 10#4 := by
  decide +kernel

theorem dispatch_h28  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 28 26) : BitVec 3) = 5#3 := by
  decide +kernel

theorem dispatch_h29  :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 28 26) : BitVec 3) = 5#3 := by
  decide +kernel

theorem dispatch_h30  :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 30 24) : BitVec 7) = 85#7 := by
  decide +kernel

theorem dispatch_h31  :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 30 24) : BitVec 7) = 85#7 := by
  decide +kernel

theorem dispatch_h32  :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 30 24) : BitVec 7) = 85#7 := by
  decide +kernel

theorem dispatch_h33  :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 30 24) : BitVec 7) = 85#7 := by
  decide +kernel

theorem dispatch_h34  :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 5) : BitVec 27) = 111680002#27 := by
  decide +kernel

theorem dispatch_h35  :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 5) : BitVec 27) = 111680002#27 := by
  decide +kernel

theorem dispatch_h36  :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 5) : BitVec 27) = 111680002#27 := by
  decide +kernel

theorem dispatch_h37  :
    (Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 5) : BitVec 27) = 111680002#27 := by
  decide +kernel

theorem dispatch_h38  :
    (Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 8) : BitVec 24) = 13960000#24 := by
  decide +kernel

theorem dispatch_h39  :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 10) : BitVec 22) = 3490000#22 := by
  decide +kernel

theorem dispatch_h40  :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 10) : BitVec 22) = 3490000#22 := by
  decide +kernel

theorem dispatch_h41  :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 10) : BitVec 22) = 3490000#22 := by
  decide +kernel

theorem dispatch_h42  :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 10) : BitVec 22) = 3490000#22 := by
  decide +kernel

theorem dispatch_h43  :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 11) : BitVec 21) = 1745000#21 := by
  decide +kernel

theorem dispatch_h44  :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 11) : BitVec 21) = 1745000#21 := by
  decide +kernel

theorem dispatch_h45  :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 12) : BitVec 20) = 872500#20 := by
  decide +kernel

theorem dispatch_h46  :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 12) : BitVec 20) = 872500#20 := by
  decide +kernel

theorem dispatch_h47  :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 19) : BitVec 13) = 6816#13 := by
  decide +kernel

theorem dispatch_h48  :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 19) : BitVec 13) = 6816#13 := by
  decide +kernel

theorem dispatch_h49  :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 19) : BitVec 13) = 6816#13 := by
  decide +kernel

theorem dispatch_h50  :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 19) : BitVec 13) = 6816#13 := by
  decide +kernel

theorem dispatch_h51  :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 20) : BitVec 12) = 3408#12 := by
  decide +kernel

theorem dispatch_h52  :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 20) : BitVec 12) = 3408#12 := by
  decide +kernel

theorem dispatch_h53  :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 20) : BitVec 12) = 3408#12 := by
  decide +kernel

theorem dispatch_h54  :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 20) : BitVec 12) = 3408#12 := by
  decide +kernel

theorem dispatch_h55  :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 21) : BitVec 11) = 1704#11 := by
  decide +kernel

theorem dispatch_h56  :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 21) : BitVec 11) = 1704#11 := by
  decide +kernel

theorem dispatch_h57  :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 21) : BitVec 11) = 1704#11 := by
  decide +kernel

theorem dispatch_h58  :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 21) : BitVec 11) = 1704#11 := by
  decide +kernel

theorem dispatch_h59  :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 21) : BitVec 11) = 1704#11 := by
  decide +kernel

theorem dispatch_h60  :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 24) : BitVec 8) = 213#8 := by
  decide +kernel

theorem dispatch_h61  :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 25) : BitVec 7) = 106#7 := by
  decide +kernel

theorem dispatch_h62  :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 26) : BitVec 6) = 53#6 := by
  decide +kernel

theorem dispatch_h63  :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 26) : BitVec 6) = 53#6 := by
  decide +kernel

theorem dispatch_h64  :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 31) : BitVec 1) = 1#1 := by
  decide +kernel

theorem dispatch_h65  :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryDispatch.DitOff.word ) 31 31) : BitVec 1) = 1#1 := by
  decide +kernel

theorem dispatch_h66  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 0 2 = 3#2 := by
  decide +kernel

theorem dispatch_h67  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 0 4 = 15#4 := by
  decide +kernel

theorem dispatch_h68  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 0 5 = 31#5 := by
  decide +kernel

theorem dispatch_h69  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 0 26 = 16990303#26 := by
  decide +kernel

theorem dispatch_h70  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 5 2 = 2#2 := by
  decide +kernel

theorem dispatch_h71  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 5 3 = 2#3 := by
  decide +kernel

theorem dispatch_h72  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 5 5 = 2#5 := by
  decide +kernel

theorem dispatch_h73  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 5 14 = 6658#14 := by
  decide +kernel

theorem dispatch_h74  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 5 16 = 6658#16 := by
  decide +kernel

theorem dispatch_h75  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 5 19 = 6658#19 := by
  decide +kernel

theorem dispatch_h76  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 8 4 = 0#4 := by
  decide +kernel

theorem dispatch_h77  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 10 1 = 0#1 := by
  decide +kernel

theorem dispatch_h78  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 10 2 = 0#2 := by
  decide +kernel

theorem dispatch_h79  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 11 1 = 0#1 := by
  decide +kernel

theorem dispatch_h80  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 12 4 = 4#4 := by
  decide +kernel

theorem dispatch_h81  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 16 3 = 3#3 := by
  decide +kernel

theorem dispatch_h82  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 19 1 = 0#1 := by
  decide +kernel

theorem dispatch_h83  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 19 5 = 0#5 := by
  decide +kernel

theorem dispatch_h84  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 21 1 = 0#1 := by
  decide +kernel

theorem dispatch_h85  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 21 2 = 0#2 := by
  decide +kernel

theorem dispatch_h86  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 24 1 = 1#1 := by
  decide +kernel

theorem dispatch_h87  :
    BitVec.slice (NativeEntryDispatch.DitOff.word ) 31 1 = 1#1 := by
  decide +kernel

theorem dispatch_hw88  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573563423#32) := by
  decide +kernel

theorem dispatch_hw89  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573563455#32) := by
  decide +kernel

theorem dispatch_hw90  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573563487#32) := by
  decide +kernel

theorem dispatch_hw91  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573751839#32) := by
  decide +kernel

theorem dispatch_hw92  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573751871#32) := by
  decide +kernel

theorem dispatch_hw93  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573751903#32) := by
  decide +kernel

theorem dispatch_hw94  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573751935#32) := by
  decide +kernel

theorem dispatch_hw95  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573751967#32) := by
  decide +kernel

theorem dispatch_hw96  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573751999#32) := by
  decide +kernel

theorem dispatch_hw97  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752031#32) := by
  decide +kernel

theorem dispatch_hw98  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752063#32) := by
  decide +kernel

theorem dispatch_hw99  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752351#32) := by
  decide +kernel

theorem dispatch_hw100  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752383#32) := by
  decide +kernel

theorem dispatch_hw101  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752415#32) := by
  decide +kernel

theorem dispatch_hw102  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752447#32) := by
  decide +kernel

theorem dispatch_hw103  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752479#32) := by
  decide +kernel

theorem dispatch_hw104  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573752543#32) := by
  decide +kernel

theorem dispatch_hw105  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573753119#32) := by
  decide +kernel

theorem dispatch_hw106  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573756031#32) := by
  decide +kernel

theorem dispatch_hw107  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3573756159#32) := by
  decide +kernel

theorem dispatch_hw108  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3600745440#32) := by
  decide +kernel

theorem dispatch_hw109  :
    ¬ ((NativeEntryDispatch.DitOff.word ) = 3602842592#32) := by
  decide +kernel

theorem dispatch (pc : Int)  :
    __DecodeA64 (real := real) pc (NativeEntryDispatch.DitOff.word ) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 703))
      if c = true then (do writeReg Register.SEE 703; decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 0#4 3#3)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_hw88, dispatch_hw89, dispatch_hw90, dispatch_hw91, dispatch_hw92, dispatch_hw93, dispatch_hw94, dispatch_hw95, dispatch_hw96, dispatch_hw97, dispatch_hw98, dispatch_hw99, dispatch_hw100, dispatch_hw101, dispatch_hw102, dispatch_hw103, dispatch_hw104, dispatch_hw105, dispatch_hw106, dispatch_hw107, dispatch_hw108, dispatch_hw109, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_BranchExcSys
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_hw88, dispatch_hw89, dispatch_hw90, dispatch_hw91, dispatch_hw92, dispatch_hw93, dispatch_hw94, dispatch_hw95, dispatch_hw96, dispatch_hw97, dispatch_hw98, dispatch_hw99, dispatch_hw100, dispatch_hw101, dispatch_hw102, dispatch_hw103, dispatch_hw104, dispatch_hw105, dispatch_hw106, dispatch_hw107, dispatch_hw108, dispatch_hw109, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int)  (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 703) :
    (__DecodeA64 (real := real) pc (word) : SailM Unit) s =
      (do writeReg Register.SEE 703; decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 0#4 3#3 : SailM Unit) s := by
  rw [dispatch real pc]
  have h : (s.regs.bank_Int .SEE <b 703) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 703)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 703) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryDispatch.DitOff
