-- Determine whether MTE2 affects the existing exact BranchTo proof.
import SDKPA.Roots
#premise_drop BR8_BranchTo.complete_pa_mte from BR8_BranchTo.complete_pa drop hFeature_MTE2
#print axioms BR8_BranchTo.complete_pa_mte
