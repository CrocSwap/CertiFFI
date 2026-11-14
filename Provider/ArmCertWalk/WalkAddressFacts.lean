import ArmCertWalk.EndpointSuffix
import GetEntry.WP

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Preserve a source-derived value field while composing the actual prefix;
the predicate concerns the returned value, never a future execution answer. -/
theorem bind_value_ensures {R α β : Type} (p : SailME R α) (k : α → SailME R β)
    (state : State) (next : β → State → Prop) (exit : R → State → Prop) (value : α → Prop)
    (hp : S1NormalME.Ensures (fun _ => True) p value)
    (hk : ∀ a other, S1Normality.Frame state other → value a → S1EntryWP.WP (k a) other next exit) :
    S1EntryWP.WP (p >>= k) state next exit := by
  obtain ⟨a, other, call, frame, field⟩ := hp state trivial
  apply S1EntryWP.bind_wp
  exact ⟨.ok a, other, call, hk a other frame field⟩

#print axioms bind_value_ensures
end ArmCertWalk
