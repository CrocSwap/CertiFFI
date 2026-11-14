import Walk.S2PAMax
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2PhysicalSize
drive_spec native0, eq0 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 0#3 .TGx_4KB s
drive_spec native1, eq1 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 1#3 .TGx_4KB s
drive_spec native2, eq2 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 2#3 .TGx_4KB s
drive_spec native3, eq3 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 3#3 .TGx_4KB s
drive_spec native4, eq4 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 4#3 .TGx_4KB s
drive_spec native5, eq5 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 5#3 .TGx_4KB s
drive_spec native6, eq6 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 6#3 .TGx_4KB s
drive_spec native7, eq7 :
  fun (paSize : Int) (s : SequentialState Regs oracleChoiceSource)
      (hPA : s.regs.bank_Int .__supported_pa_size = paSize) =>
    AArch64_PhysicalAddressSize 0#1 7#3 .TGx_4KB s
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State Int
noncomputable def native (paSize : Int) (ps : BitVec 3) (s : State) : Result :=
  if ps = 0#3 then native0 paSize s else
  if ps = 1#3 then native1 paSize s else
  if ps = 2#3 then native2 paSize s else
  if ps = 3#3 then native3 paSize s else
  if ps = 4#3 then native4 paSize s else
  if ps = 5#3 then native5 paSize s else
  if ps = 6#3 then native6 paSize s else
  native7 paSize s

theorem complete (paSize : Int) (ps : BitVec 3) (s : State)
    (hPA : s.regs.bank_Int .__supported_pa_size = paSize) :
    AArch64_PhysicalAddressSize 0#1 ps .TGx_4KB s = native paSize ps s := by
  by_cases h0 : ps = 0#3
  · simpa [native, h0] using eq0 paSize s hPA
  by_cases h1 : ps = 1#3
  · simpa [native, h1] using eq1 paSize s hPA
  by_cases h2 : ps = 2#3
  · simpa [native, h2] using eq2 paSize s hPA
  by_cases h3 : ps = 3#3
  · simpa [native, h3] using eq3 paSize s hPA
  by_cases h4 : ps = 4#3
  · simpa [native, h4] using eq4 paSize s hPA
  by_cases h5 : ps = 5#3
  · simpa [native, h5] using eq5 paSize s hPA
  by_cases h6 : ps = 6#3
  · simpa [native, h6] using eq6 paSize s hPA
  have h7 : ps = 7#3 := by
    have hb := ps.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  simpa [native, h7] using eq7 paSize s hPA
attribute [step_summary] complete
#print axioms complete
end S2PhysicalSize
