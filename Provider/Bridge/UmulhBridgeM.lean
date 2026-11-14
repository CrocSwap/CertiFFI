import Bridge.UmulhDecode
import Bridge.Awc
import Bridge.Mul
import Bridge.RootsPF
import Bridge.StepM
import BridgeV2.BoundaryV2
import Bridge.MovzBridge
import Bridge.Proj
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2 ArmBridge.Movz
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.UmulhBridgeMLNSym.
namespace ArmBridge.Umulh

theorem b01 : ((0#1 : BitVec 1) == 1#1) = false := rfl

theorem b11 : ((1#1 : BitVec 1) == 1#1) = true := rfl

theorem wl64 : (if (1#1 : BitVec 1) = 1#1 then 64 else 32) = 64 := rfl

theorem wl32 : (if (0#1 : BitVec 1) = 1#1 then 64 else 32) = 32 := rfl

end ArmBridge.Umulh

