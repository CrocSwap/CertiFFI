/-! CertiFFI claim cards: typed, registered inputs.

Every hypothesis of a headline (card) theorem has one of these kinds. Each kind is a distinct `Prop` structure that
carries a registry id (a string literal) and, for `Premise`, an evidence grade. A hypothesis that is not wrapped in
one of these kinds is UNCLASSIFIED; `#print premises` reports it as an error and `certiffi certify` refuses the card.
`Proved` has no wrapper: proved facts are lemmas in the closure, not hypotheses.

The structures are transparent wrappers (`holds` projects the underlying proposition), so a card theorem is proved by
applying the sealed release theorem to the projections: the card restates the sealed statement with every input typed. -/
namespace CertiFFI.Claim

/-- Evidence grade of a catalogued premise. -/
inductive Grade where
  | trm        -- architecture reference manual / TRM text
  | measured   -- measured on the target platform
  | sanitized  -- established by a sanitizer/checker run
  | audited    -- established by a human audit
  | decided    -- decision of record (policy choice)
  | interim    -- interim premise scheduled for elimination
  deriving Repr, DecidableEq, Inhabited

/-- A decidable check evaluated on the actual sealed binary / deployment (at certify or final-binding time). -/
structure RunCheck (id : String) (P : Prop) : Prop where
  intro ::
  holds : P

/-- A catalogued hardware/OS assumption with an evidence grade. -/
structure Premise (id : String) (grade : Grade) (P : Prop) : Prop where
  intro ::
  holds : P

/-- What the calling code must guarantee. -/
structure CallerContract (id : String) (P : Prop) : Prop where
  intro ::
  holds : P

/-- What the machine / OS setup must guarantee. -/
structure DeploymentObligation (id : String) (P : Prop) : Prop where
  intro ::
  holds : P

end CertiFFI.Claim
