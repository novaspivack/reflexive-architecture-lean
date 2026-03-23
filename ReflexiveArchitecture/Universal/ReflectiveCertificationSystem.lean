/-
  EPIC_019 Phase I — minimal abstract floor for universal certification/realization comparison.

  Weaker than the NEMS/APS/IC layer interfaces: only carriers, `compare`, a canonical
  region on bare objects, and a single soundness `Prop` placeholder (to be discharged
  per instance).
-/

universe u

namespace ReflexiveArchitecture.Universal

/-- Reflective certification system: bare certificates, realized witnesses, comparison,
canonical region on `Bare`, and a packaged soundness statement. -/
structure ReflectiveCertificationSystem (Bare Realized : Type u) where
  compare : Realized → Bare
  Canonical : Bare → Prop
  /-- Intended: global or schematic soundness of `compare` w.r.t. intended semantics. -/
  Sound : Prop

end ReflexiveArchitecture.Universal
