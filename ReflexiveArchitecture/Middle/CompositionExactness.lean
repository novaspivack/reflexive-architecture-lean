/-
  Projection theorems from the middle interface.
-/

import ReflexiveArchitecture.Middle.Interface

universe u

namespace ReflexiveArchitecture.Middle

theorem composition_from_tracking_and_gluing {S : Type u} [M : RealizationLayer S]
    (h : M.HasFiniteTracking ∧ M.HasGluing) :
    M.ICompIdx :=
  (M.comp_iff_finiteTracking_and_gluing).2 h

theorem tracking_and_gluing_from_composition {S : Type u} [M : RealizationLayer S]
    (h : M.ICompIdx) :
    M.HasFiniteTracking ∧ M.HasGluing :=
  (M.comp_iff_finiteTracking_and_gluing).1 h

end ReflexiveArchitecture.Middle
