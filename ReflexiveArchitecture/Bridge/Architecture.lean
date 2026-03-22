/-
  Bundled reflexive architecture: outer + middle + inner interfaces,
  plus two cross-layer coherence axioms grounding the non-erasure principle.
-/

import ReflexiveArchitecture.Outer.Interface
import ReflexiveArchitecture.Middle.Interface
import ReflexiveArchitecture.Inner.Interface

universe u

namespace ReflexiveArchitecture.Bridge

/-- A reflexive architecture bundles all three abstract layers and carries two cross-layer
coherence axioms expressing the non-erasure constraint between outer and inner.

**Coherence axiom 1** (positive direction):
If some internal theory has semantic remainder, then inner enriched irreducibility holds.
"Outer semantic non-exhaustion forces inner enriched structure."

**Coherence axiom 2** (negative direction):
If every internal theory is totally exhausted without remainder, then inner enriched
irreducibility fails.
"Outer total exhaustion is incompatible with inner enriched structure."

Together these form a biconditional: `EnrichedIrreducibility ↔ ∃ T, SemanticRemainder T`
(under the assumption that `InternalTheory` is satisfied for the existential).

These are minimal, non-smuggling constraints: they state only the abstract relationship
between outer semantic content and inner enrichment, without identifying any specific
NEMS/IC object. Both directions are needed to prove the full non-erasure principle. -/
class Architecture (A : Type u) extends
    Outer.ReflexiveLayer A,
    Middle.RealizationLayer A,
    Inner.CertificationLayer A where
  /-- Positive coherence: outer remainder forces inner enriched irreducibility. -/
  outer_remainder_forces_inner_enrichment :
    (∃ T, InternalTheory T ∧ SemanticRemainder T) → EnrichedIrreducibility
  /-- Negative coherence: outer total exhaustion kills inner enriched irreducibility. -/
  outer_exhaustion_kills_inner_enrichment :
    (∀ T, InternalTheory T → TotalOn T ∧ ¬ SemanticRemainder T) →
      ¬ EnrichedIrreducibility

end ReflexiveArchitecture.Bridge
