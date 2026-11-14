import Pilot.Driver
import Pilot.EvalProfile
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
namespace GPRSummary
def key (n : Nat) : Fin 31 :=
  match n with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | 4 => ⟨4, by decide⟩
  | 5 => ⟨5, by decide⟩
  | 6 => ⟨6, by decide⟩
  | 7 => ⟨7, by decide⟩
  | 8 => ⟨8, by decide⟩
  | 9 => ⟨9, by decide⟩
  | 10 => ⟨10, by decide⟩
  | 11 => ⟨11, by decide⟩
  | 12 => ⟨12, by decide⟩
  | 13 => ⟨13, by decide⟩
  | 14 => ⟨14, by decide⟩
  | 15 => ⟨15, by decide⟩
  | 16 => ⟨16, by decide⟩
  | 17 => ⟨17, by decide⟩
  | 18 => ⟨18, by decide⟩
  | 19 => ⟨19, by decide⟩
  | 20 => ⟨20, by decide⟩
  | 21 => ⟨21, by decide⟩
  | 22 => ⟨22, by decide⟩
  | 23 => ⟨23, by decide⟩
  | 24 => ⟨24, by decide⟩
  | 25 => ⟨25, by decide⟩
  | 26 => ⟨26, by decide⟩
  | 27 => ⟨27, by decide⟩
  | 28 => ⟨28, by decide⟩
  | 29 => ⟨29, by decide⟩
  | _ => ⟨30, by decide⟩
theorem read_complete (n : Nat) (s : SequentialState Regs oracleChoiceSource) :
    read_gpr n s = .ok (s.regs.gpr[(key n).val]) s := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases n with
              | zero => rfl
              | succ n =>
                cases n with
                | zero => rfl
                | succ n =>
                  cases n with
                  | zero => rfl
                  | succ n =>
                    cases n with
                    | zero => rfl
                    | succ n =>
                      cases n with
                      | zero => rfl
                      | succ n =>
                        cases n with
                        | zero => rfl
                        | succ n =>
                          cases n with
                          | zero => rfl
                          | succ n =>
                            cases n with
                            | zero => rfl
                            | succ n =>
                              cases n with
                              | zero => rfl
                              | succ n =>
                                cases n with
                                | zero => rfl
                                | succ n =>
                                  cases n with
                                  | zero => rfl
                                  | succ n =>
                                    cases n with
                                    | zero => rfl
                                    | succ n =>
                                      cases n with
                                      | zero => rfl
                                      | succ n =>
                                        cases n with
                                        | zero => rfl
                                        | succ n =>
                                          cases n with
                                          | zero => rfl
                                          | succ n =>
                                            cases n with
                                            | zero => rfl
                                            | succ n =>
                                              cases n with
                                              | zero => rfl
                                              | succ n =>
                                                cases n with
                                                | zero => rfl
                                                | succ n =>
                                                  cases n with
                                                  | zero => rfl
                                                  | succ n =>
                                                    cases n with
                                                    | zero => rfl
                                                    | succ n =>
                                                      cases n with
                                                      | zero => rfl
                                                      | succ n =>
                                                        cases n with
                                                        | zero => rfl
                                                        | succ n =>
                                                          cases n with
                                                          | zero => rfl
                                                          | succ n =>
                                                            cases n with
                                                            | zero => rfl
                                                            | succ n =>
                                                              rfl
attribute [step_summary] read_complete
#print axioms read_complete
theorem write_complete (n : Nat) (v : BitVec 64) (s : SequentialState Regs oracleChoiceSource) :
    write_gpr n v s = .ok () {s with regs := {s.regs with
      gpr := s.regs.gpr.set (key n).val v (key n).isLt}} := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases n with
              | zero => rfl
              | succ n =>
                cases n with
                | zero => rfl
                | succ n =>
                  cases n with
                  | zero => rfl
                  | succ n =>
                    cases n with
                    | zero => rfl
                    | succ n =>
                      cases n with
                      | zero => rfl
                      | succ n =>
                        cases n with
                        | zero => rfl
                        | succ n =>
                          cases n with
                          | zero => rfl
                          | succ n =>
                            cases n with
                            | zero => rfl
                            | succ n =>
                              cases n with
                              | zero => rfl
                              | succ n =>
                                cases n with
                                | zero => rfl
                                | succ n =>
                                  cases n with
                                  | zero => rfl
                                  | succ n =>
                                    cases n with
                                    | zero => rfl
                                    | succ n =>
                                      cases n with
                                      | zero => rfl
                                      | succ n =>
                                        cases n with
                                        | zero => rfl
                                        | succ n =>
                                          cases n with
                                          | zero => rfl
                                          | succ n =>
                                            cases n with
                                            | zero => rfl
                                            | succ n =>
                                              cases n with
                                              | zero => rfl
                                              | succ n =>
                                                cases n with
                                                | zero => rfl
                                                | succ n =>
                                                  cases n with
                                                  | zero => rfl
                                                  | succ n =>
                                                    cases n with
                                                    | zero => rfl
                                                    | succ n =>
                                                      cases n with
                                                      | zero => rfl
                                                      | succ n =>
                                                        cases n with
                                                        | zero => rfl
                                                        | succ n =>
                                                          cases n with
                                                          | zero => rfl
                                                          | succ n =>
                                                            cases n with
                                                            | zero => rfl
                                                            | succ n =>
                                                              rfl
attribute [step_summary] write_complete
#print axioms write_complete
end GPRSummary
