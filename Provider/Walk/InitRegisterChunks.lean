import Walk.InitTLBProperties
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace InitRegisterChunks
open InitTLBProperties

theorem chunk0 : Keeps (initialize_registers_0 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk1 : Keeps (initialize_registers_1 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk2 : Keeps (initialize_registers_2 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk3 : Keeps (initialize_registers_3 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk4 : Keeps (initialize_registers_4 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk5 : Keeps (initialize_registers_5 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk6 : Keeps (initialize_registers_6 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk7 : Keeps (initialize_registers_7 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk8 : Keeps (initialize_registers_8 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk9 : Keeps (initialize_registers_9 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk10 : Keeps (initialize_registers_10 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk11 : Keeps (initialize_registers_11 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk12 : Keeps (initialize_registers_12 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk13 : Keeps (initialize_registers_13 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk14 : Keeps (initialize_registers_14 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk15 : Keeps (initialize_registers_15 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk16 : Keeps (initialize_registers_16 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk17 : Keeps (initialize_registers_17 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk18 : Keeps (initialize_registers_18 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk19 : Keeps (initialize_registers_19 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk20 : Keeps (initialize_registers_20 ()) :=
  of_observation _ (fun _ => by rfl)

theorem chunk21 : Keeps (initialize_registers_21 ()) :=
  of_observation _ (fun _ => by rfl)

theorem all_chunks : Keeps (initialize_registers ()) := by
  unfold initialize_registers
  apply InitTLBProperties.bind
  · exact chunk0
  · intro _
    apply InitTLBProperties.bind
    · exact chunk1
    · intro _
      apply InitTLBProperties.bind
      · exact chunk2
      · intro _
        apply InitTLBProperties.bind
        · exact chunk3
        · intro _
          apply InitTLBProperties.bind
          · exact chunk4
          · intro _
            apply InitTLBProperties.bind
            · exact chunk5
            · intro _
              apply InitTLBProperties.bind
              · exact chunk6
              · intro _
                apply InitTLBProperties.bind
                · exact chunk7
                · intro _
                  apply InitTLBProperties.bind
                  · exact chunk8
                  · intro _
                    apply InitTLBProperties.bind
                    · exact chunk9
                    · intro _
                      apply InitTLBProperties.bind
                      · exact chunk10
                      · intro _
                        apply InitTLBProperties.bind
                        · exact chunk11
                        · intro _
                          apply InitTLBProperties.bind
                          · exact chunk12
                          · intro _
                            apply InitTLBProperties.bind
                            · exact chunk13
                            · intro _
                              apply InitTLBProperties.bind
                              · exact chunk14
                              · intro _
                                apply InitTLBProperties.bind
                                · exact chunk15
                                · intro _
                                  apply InitTLBProperties.bind
                                  · exact chunk16
                                  · intro _
                                    apply InitTLBProperties.bind
                                    · exact chunk17
                                    · intro _
                                      apply InitTLBProperties.bind
                                      · exact chunk18
                                      · intro _
                                        apply InitTLBProperties.bind
                                        · exact chunk19
                                        · intro _
                                          apply InitTLBProperties.bind
                                          · exact chunk20
                                          · intro _
                                            exact chunk21

#print axioms all_chunks
end InitRegisterChunks
