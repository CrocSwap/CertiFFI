import Walk.S1LeafComposition
import Walk.S1EL10LeafPerms
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S1LeafBoth
open S1Normality

def Regimes (regime : Regime) : Prop := regime = .Regime_EL10 ∨ regime = .Regime_EL20

theorem permissions_normal (regime : Regime) (hRegime : Regimes regime)
    (p : Permissions) (d : BitVec 64) (wp : S1TTWParams) (hD128 : wp.d128 = 0#1) :
    Normal (AArch64_S1ApplyOutputPerms p d regime wp) := by
  rcases hRegime with rfl | rfl
  · exact S1EL10LeafPerms.normal p d wp hD128
  · exact S1Normality.permissions_normal p d wp hD128

theorem normal_shape (regime : Regime) (hRegime : Regimes regime)
    (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLevel : 1 ≤ current.level ∧ current.level ≤ 3) :
    S1NormalPost.Ensures
      (AArch64_S1NextWalkStateLeaf current s2fs1mro regime .SS_NonSecure wp d)
      (S1LeafShape.Shape wp current d) := by
  have hUP : HasUnprivileged regime = true := by
    rcases hRegime with rfl | rfl <;> decide
  exact S1LeafComposition.normal_shape regime current s2fs1mro wp d hD128 hDS hTG
    hAIE hMAIR hPAS hLevel hUP (fun p => permissions_normal regime hRegime p d wp hD128)
#print axioms normal_shape
end S1LeafBoth
