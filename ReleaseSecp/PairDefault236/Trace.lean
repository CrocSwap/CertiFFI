import PairDefault236.Control
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace PairDefault236.Trace
abbrev State := NativeMteTagCheck.State
abbrev Frame := NativeMteTagCheck.StatusTrace.TraceFrame
abbrev frame_trans := @NativeMteTagCheck.StatusTrace.frame_trans
end PairDefault236.Trace
