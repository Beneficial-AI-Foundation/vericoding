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
-- LLM HELPER
@[simp] lemma ChebyshevPoly.coef_get {n : Nat} (c : Vector Float n) (i : Fin n) :
  ({ coef := c } : ChebyshevPoly n).coef.get i = c.get i := rfl

-- LLM HELPER
@[simp] lemma ChebyshevPoly.domain_min_default {n : Nat} (c : Vector Float n) :
  ({ coef := c } : ChebyshevPoly n).domain_min = -1.0 := rfl

-- LLM HELPER
@[simp] lemma ChebyshevPoly.domain_max_default {n : Nat} (c : Vector Float n) :
  ({ coef := c } : ChebyshevPoly n).domain_max = 1.0 := rfl

-- LLM HELPER
@[simp] lemma ChebyshevPoly.window_min_default {n : Nat} (c : Vector Float n) :
  ({ coef := c } : ChebyshevPoly n).window_min = -1.0 := rfl

-- LLM HELPER
@[simp] lemma ChebyshevPoly.window_max_default {n : Nat} (c : Vector Float n) :
  ({ coef := c } : ChebyshevPoly n).window_max = 1.0 := rfl

-- LLM HELPER
lemma float_neg_one_lt_one : (-1.0 : Float) < 1.0 := by native_decide
-- </vc-helpers>

-- <vc-definitions>
def chebyshev {n : Nat} (coef : Vector Float n) : Id (ChebyshevPoly n) :=
  pure { coef := coef }
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
  simpa [chebyshev] using
    (by
      intro (_h : True)
      constructor
      · intro _; rfl
      · constructor
        · simp [ChebyshevPoly.domain_min_default]
        · constructor
          · simp [ChebyshevPoly.domain_max_default]
          · constructor
            · simp [ChebyshevPoly.window_min_default]
            · constructor
              · simp [ChebyshevPoly.window_max_default]
              · constructor
                · simpa [ChebyshevPoly.domain_min_default, ChebyshevPoly.domain_max_default] using float_neg_one_lt_one
                · simpa [ChebyshevPoly.window_min_default, ChebyshevPoly.window_max_default] using float_neg_one_lt_one
    )
-- </vc-theorems>
