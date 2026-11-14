import BR8.CBZ
import BR8.BCond
import BR8.BranchTo
import SDKPA.PremiseDrop
/-! DERIVED: PA-free branch roots. `#premise_drop` re-checks the ORIGINAL
proof in the kernel and drops ONLY the unused hPA binder (the __supported_pa_size pin). -/
#premise_drop BR_CBZ.complete_pa from BR_CBZ.complete drop hPA
#premise_drop BR_BCondH.complete_pa from BR_BCondH.complete drop hPA
#premise_drop BR8_BranchTo.complete_pa from BR8_BranchTo.complete drop hPA
#print axioms BR_CBZ.complete_pa
#print axioms BR_BCondH.complete_pa
#print axioms BR8_BranchTo.complete_pa
