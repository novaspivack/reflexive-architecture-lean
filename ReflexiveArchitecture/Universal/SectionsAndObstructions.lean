/-
  EPIC_019 Phase I — sections (right inverses), surjectivity, and a minimal liftability /
  obstruction interface (to be instantiated per domain).
-/

import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem
import ReflexiveArchitecture.Universal.FiberBasics
import ReflexiveArchitecture.Universal.ExhaustionDefinitions

universe u

namespace ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-- `s` is a (set-theoretic) section: `compare (s b) = b` for all `b`
(`LeftInverse compare s`, i.e. `compare ∘ s = id`). -/
def IsSection (s : Bare → Realized) : Prop :=
  Function.LeftInverse S.compare s

theorem section_implies_surjective {s : Bare → Realized} (h : IsSection S s) :
    Function.Surjective S.compare :=
  h.surjective

/-- Existence of some section implies `compare` is surjective. -/
theorem surjective_of_strong_exhaustive (h : StrongExhaustive S) :
    Function.Surjective S.compare :=
  strong_exhaustive_implies_surjective S h

/-- Abstract lift predicate relative to a realizability witness `P`. -/
def LiftableWith (P : Realized → Prop) (b : Bare) : Prop :=
  ∃ x : Realized, S.compare x = b ∧ P x

/-- Trivial obstruction type placeholder (many domains refine this). -/
inductive TrivialObstruction : Type u where
  | none

/-- Minimal obstruction assignment (domain-specific refinements replace this). -/
structure ObstructionAssignment (Bare Ob : Type u) where
  val : Bare → Ob

def ObstructionFree {Bare Ob : Type u} (trivial : Ob) (obs : ObstructionAssignment Bare Ob) : Prop :=
  ∀ b : Bare, obs.val b = trivial

theorem liftable_of_section {s : Bare → Realized} (hsec : IsSection S s) (P : Realized → Prop)
    (hP : ∀ b, P (s b)) (b : Bare) : LiftableWith S P b :=
  ⟨s b, hsec b, hP b⟩

end ReflexiveArchitecture.Universal
