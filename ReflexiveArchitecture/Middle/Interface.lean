/-
  Middle layer — APS-style indexed composition / realization interface.
-/

import Mathlib.Tactic

universe u

namespace ReflexiveArchitecture.Middle

/-- Abstract indexed composition exactness: composition iff tracking ∧ gluing. -/
class RealizationLayer (S : Type u) where
  HasFiniteTracking : Prop
  HasGluing : Prop
  ICompIdx : Prop
  IRecIdx : Prop

  comp_iff_finiteTracking_and_gluing :
    ICompIdx ↔ HasFiniteTracking ∧ HasGluing

end ReflexiveArchitecture.Middle
