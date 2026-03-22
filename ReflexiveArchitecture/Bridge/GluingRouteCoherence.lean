/-
  Bridge P1 — middle gluing + finite tracking + adequate routes jointly cohere with inner
  route necessity and strict refinement when bare canonicity is present.

  APS-style content: global composition is exactly tracking ∧ gluing.
  IC-style content: adequate routes force universal route necessity, hence strict refinement
  once bare canonicity holds.

  This file makes the *interaction* explicit: the conjunction of middle gluing data and
  inner adequacy is a single "local-to-global + route discipline" package feeding both
  `ICompIdx` and the inner residue chain (under canonical bare certification).

  It does *not* identify middle routes with inner `Route` types — only logical consequences
  from the bundled `Architecture` hypotheses.
-/

import ReflexiveArchitecture.Bridge.Architecture
import ReflexiveArchitecture.Middle.CompositionExactness
import ReflexiveArchitecture.Inner.ResiduePackage

universe u

namespace ReflexiveArchitecture.Bridge

open Middle Inner

/-- Joint witness: finite tracking, gluing, and at least one adequate certification route. -/
def GlueRouteCoherent (A : Type u) [R : Architecture A] : Prop :=
  R.HasFiniteTracking ∧ R.HasGluing ∧ (∃ r, R.AdequateRoute r)

theorem glue_route_coherent_implies_composition {A : Type u} [R : Architecture A]
    (h : GlueRouteCoherent A) :
    R.ICompIdx := by
  rcases h with ⟨hFT, hGlue, _⟩
  exact composition_from_tracking_and_gluing (M := R.toRealizationLayer) ⟨hFT, hGlue⟩

theorem glue_route_coherent_implies_composition_and_route_necessity {A : Type u}
    [R : Architecture A] (h : GlueRouteCoherent A) :
    R.ICompIdx ∧ R.UniversalRouteNecessity := by
  rcases h with ⟨hFT, hGlue, hAdeq⟩
  refine ⟨composition_from_tracking_and_gluing (M := R.toRealizationLayer) ⟨hFT, hGlue⟩, ?_⟩
  exact R.adequate_implies_route_necessity hAdeq

/-- Gluing + adequacy + canonical bare certificate yield the full inner residue chain
except `ReflectiveSplit` listed explicitly first in `inner_residue_package`. -/
theorem glue_route_coherent_and_canonical_implies_inner_residue {A : Type u} [R : Architecture A]
    (h : GlueRouteCoherent A) (hCanon : R.CanonicalBareCertificate) :
    R.ReflectiveSplit ∧ R.UniversalRouteNecessity ∧ R.StrictRefinement ∧ R.FiberNontriviality :=
  inner_residue_package (I := R.toCertificationLayer) hCanon h.2.2

/-- The coherent glue/route package together with canonical bare certification yields
middle composition *and* strict refinement (hence nontrivial fiber). -/
theorem glue_route_coherent_canonical_implies_composition_and_strict_refinement
    {A : Type u} [R : Architecture A] (h : GlueRouteCoherent A)
    (hCanon : R.CanonicalBareCertificate) :
    R.ICompIdx ∧ R.StrictRefinement ∧ R.FiberNontriviality := by
  rcases glue_route_coherent_and_canonical_implies_inner_residue h hCanon with
    ⟨_, _, hRef, hFib⟩
  refine ⟨glue_route_coherent_implies_composition h, hRef, hFib⟩

/-- Characterization: `GlueRouteCoherent` is exactly the middle ∧ inner existential
fragment used in the layered theorem *before* barrier and canonical hypotheses. -/
theorem glue_route_coherent_iff {A : Type u} [R : Architecture A] :
    GlueRouteCoherent A ↔ R.HasFiniteTracking ∧ R.HasGluing ∧ (∃ r, R.AdequateRoute r) :=
  Iff.rfl

end ReflexiveArchitecture.Bridge
