/-
  EPIC_019 Phase III — a tiny synthetic instance: product projections are not
  injective, hence abstract `NonExhaustive` with an explicit fiber over a bare value.
  No dependency on IC/NEMS; useful as a second discharge of the universal layer.
-/

import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem
import ReflexiveArchitecture.Universal.ExhaustionDefinitions

namespace ReflexiveArchitecture.Universal.Instances

open ReflexiveArchitecture.Universal

/-- Toy RCS: bare = first projection of a pair; canonical predicate trivial. -/
@[reducible]
def toyProductRCS : ReflectiveCertificationSystem Bool (Bool × Bool) where
  compare := fun p => p.1
  Canonical := fun _ => True
  Sound := True

theorem toyProduct_nonExhaustive : NonExhaustive toyProductRCS := by
  refine ⟨(true, false), (true, true), ?_, ?_⟩
  · intro h
    cases h
  · rfl

theorem toyProduct_not_minimal : ¬ MinimalExhaustive toyProductRCS :=
  (nonExhaustive_iff_not_minimal toyProductRCS).1 toyProduct_nonExhaustive

end ReflexiveArchitecture.Universal.Instances
