/-
  Abstract "collapse" predicates used for the stratified non-collapse theorem.
  Each field is an implication from structural conclusions to the negation of a flattening reading.
-/

import ReflexiveArchitecture.Bridge.Architecture

universe u

namespace ReflexiveArchitecture.Bridge

/-- Optional collapse/failure-of-stratification predicates with defeat axioms. -/
class CollapsePredicates (A : Type u) [R : Architecture A] where
  SemanticCollapse : Prop
  RealizationFlattening : Prop
  CertificationCollapse : Prop

  semantic_collapse_defeated :
    (∀ T, R.InternalTheory T → R.SemanticRemainder T ∨ ¬ R.TotalOn T) → ¬ SemanticCollapse

  realization_flattening_defeated :
    R.ICompIdx → ¬ RealizationFlattening

  certification_collapse_defeated :
    R.ReflectiveSplit ∧ R.StrictRefinement → ¬ CertificationCollapse

end ReflexiveArchitecture.Bridge
