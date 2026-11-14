import Bridge.AdcDecode
import Bridge.Awc
import Bridge.RootsPF
import Bridge.StepM
import BridgeV2.BoundaryV2
import Bridge.MovzBridge
import Bridge.Proj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2 ArmBridge.Movz
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.AdcBridgeMLNSym.
namespace ArmBridge.Adcs

theorem b01 : ((0#1 : BitVec 1) == 1#1) = false := rfl

theorem b11 : ((1#1 : BitVec 1) == 1#1) = true := rfl

theorem wl64 : (if (1#1 : BitVec 1) = 1#1 then 64 else 32) = 64 := rfl

theorem wl32 : (if (0#1 : BitVec 1) = 1#1 then 64 else 32) = 32 := rfl

theorem decode_adc_eq (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (S : BitVec 1) (op : BitVec 1) (sf : BitVec 1) :
    decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf = decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf := by
  unfold decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry
  rfl

theorem decode_sbc_eq (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (S : BitVec 1) (op : BitVec 1) (sf : BitVec 1) :
    decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf = decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf := by
  unfold decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry
  rfl

theorem decode_sbcs_eq (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (S : BitVec 1) (op : BitVec 1) (sf : BitVec 1) :
    decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf = decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf := by
  unfold decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry
  rfl

end ArmBridge.Adcs

