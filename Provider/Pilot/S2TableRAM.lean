import ArmFull
open Sail ArmFull ArmFull.Functions
namespace S2TableRAM
/- Named E5a premise approved by the release owner C41, bus 20261105T230127.452622Z-1997.
   Apply to every reached TTBR/VTTBR and next-level table physical address. -/
def OrdinaryRAM (pa : BitVec 56) : Prop :=
  pa.extractLsb' 16 40 ≠ GIC_BASE.zeroExtend 40 ∧
  pa.extractLsb' 16 40 ≠ UART_BASE.zeroExtend 40

/-- `tableFetch` is the set of physical descriptor addresses reached by the walk.
    The intended named hypothesis is `hTableRAM : TablesInRAM tableFetch`. -/
def TablesInRAM (tableFetch : BitVec 56 → Prop) : Prop :=
  ∀ pa, tableFetch pa → OrdinaryRAM pa
end S2TableRAM
