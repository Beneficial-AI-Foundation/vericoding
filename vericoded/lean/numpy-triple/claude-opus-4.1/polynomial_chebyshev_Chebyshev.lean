import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Structure representing a Chebyshev polynomial with coefficients and domain/window mapping -/
structure ChebyshevPoly (n : Nat) where
  /-- Coefficients of the Chebyshev polynomial in increasing degree order -/
  coef : Vector Float n
  /-- Domain interval [domain_min, domain_max] -/
  domain_min : Float := -1.0
  domain_max : Float := 1.0
  /-- Window interval [window_min, window_max] -/
  window_min : Float := -1.0
  window_max : Float := 1.0
-- </vc-preamble>

-- <vc-helpers>
-- Helper definitions for working with Chebyshev polynomials
-- LLM HELPER
def defaultDomainMin : Float := -1.0
-- LLM HELPER
def defaultDomainMax : Float := 1.0
-- LLM HELPER
def defaultWindowMin : Float := -1.0
-- LLM HELPER
def defaultWindowMax : Float := 1.0

-- LLM HELPER
lemma default_domain_valid : defaultDomainMin < defaultDomainMax := by
  unfold defaultDomainMin defaultDomainMax
  native_decide

-- LLM HELPER
lemma default_window_valid : defaultWindowMin < defaultWindowMax := by
  unfold defaultWindowMin defaultWindowMax
  native_decide
-- </vc-helpers>

-- <vc-definitions>
def chebyshev {n : Nat} (coef : Vector Float n) : Id (ChebyshevPoly n) :=
  pure {
    coef := coef,
    domain_min := defaultDomainMin,
    domain_max := defaultDomainMax,
    window_min := defaultWindowMin,
    window_max := defaultWindowMax
  }
-- </vc-definitions>

-- <vc-theorems>
theorem chebyshev_spec {n : Nat} (coef : Vector Float n) :
    ⦃⌜True⌝⦄
    chebyshev coef
    ⦃⇓result => ⌜-- Coefficients are preserved
                 (∀ i : Fin n, result.coef.get i = coef.get i) ∧
                 -- Default domain is [-1, 1]
                 result.domain_min = -1.0 ∧
                 result.domain_max = 1.0 ∧
                 -- Default window is [-1, 1]
                 result.window_min = -1.0 ∧
                 result.window_max = 1.0 ∧
                 -- Domain interval is valid
                 result.domain_min < result.domain_max ∧
                 -- Window interval is valid
                 result.window_min < result.window_max⌝⦄ := by
  unfold chebyshev
  unfold defaultDomainMin defaultDomainMax defaultWindowMin defaultWindowMax
  simp [pure]
  intro _
  constructor
  · intro i
    rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · -- Domain interval is valid: -1.0 < 1.0
              exact default_domain_valid
            · -- Window interval is valid: -1.0 < 1.0
              exact default_window_valid
-- </vc-theorems>
