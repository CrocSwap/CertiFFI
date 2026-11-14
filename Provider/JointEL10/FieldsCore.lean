-- Generic EL20 walk-parameter field predicates split out of JointEL10.Fields20 ((3) A6);
-- definitions byte-identical, constant names unchanged.
import JointEL10.Get20
import JointEL10.Regime20
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.JointSAT.EL20.Fields
open S1Normality ArmCert.Eval.JointSAT

/-- Extra walk-parameter facts for memory's M1-b (a1c1), lower VA range; v7: GB10 real
    HA=HD=1 (FEAT_HAFDBS in the witness vector, TCR_EL2.HA/HD set). -/
def Fields (wp : S1TTWParams) : Prop :=
  wp.ee = 0#1 ∧ wp.wxn = 0#1 ∧ wp.ha = 1#1 ∧ wp.hd = 1#1 ∧ wp.pie = 0#1 ∧
    wp.nfd = 0#1 ∧ wp.e0pd = 0#1 ∧ wp.haft = 0#1

def Good (_s : State) : EStateM.Result (Sail.Error exception) State S1TTWParams → Prop
  | .ok wp _ => Fields wp
  | .error _ _ => False

end ArmCert.Eval.JointSAT.EL20.Fields
