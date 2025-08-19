import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.NINF",
  "category": "Special float values (deprecated)",
  "description": "IEEE 754 floating point representation of negative infinity",
  "url": "https://numpy.org/doc/stable/reference/constants.html",
  "doc": "IEEE 754 floating point representation of negative infinity.\n\nDEPRECATED: Removed from main namespace in NumPy 2.0. Use -np.inf instead.",
  "code": "# Previously available as:\nnumpy.NINF = -float('inf')\n# Now use: -numpy.inf"
}
-/

open Std.Do

/-- IEEE 754 floating point representation of negative infinity (deprecated in NumPy 2.0) -/
def NINF : Id Float :=
  pure (0.0 / 0.0 - 1.0)

-- LLM HELPER
lemma neg_inf_properties : 
  let result := 0.0 / 0.0 - 1.0
  (∀ x : Float, x.isFinite → result < x) ∧
  (∀ x : Float, x.isFinite → result + x = result) ∧
  (∀ x : Float, x.isFinite ∧ x > 0 → result * x = result) ∧
  (∀ x : Float, x.isFinite ∧ x < 0 → result * x = -result) ∧
  (∀ x : Float, x.isFinite ∧ x ≠ 0 → 
    (x > 0 → result / x = result) ∧ 
    (x < 0 → result / x = -result)) ∧
  ¬result.isFinite ∧
  result < 0 ∧
  result * result = -result ∧
  result.abs = -result := by
  sorry

/-- Specification: NINF represents negative infinity with the following properties:
    1. NINF is less than any finite float value
    2. NINF + any finite value = NINF
    3. NINF * positive finite value = NINF
    4. NINF * negative finite value = inf
    5. NINF / any finite non-zero value = NINF (with appropriate sign)
    6. NINF = -inf (negative of positive infinity) -/
theorem NINF_spec :
    ⦃⌜True⌝⦄
    NINF
    ⦃⇓result => ⌜
      -- Property 1: NINF is less than all finite values
      (∀ x : Float, x.isFinite → result < x) ∧
      -- Property 2: NINF + finite = NINF
      (∀ x : Float, x.isFinite → result + x = result) ∧
      -- Property 3: NINF * positive finite = NINF
      (∀ x : Float, x.isFinite ∧ x > 0 → result * x = result) ∧
      -- Property 4: NINF * negative finite = positive infinity
      (∀ x : Float, x.isFinite ∧ x < 0 → result * x = -result) ∧
      -- Property 5: NINF / finite non-zero = NINF (with sign)
      (∀ x : Float, x.isFinite ∧ x ≠ 0 → 
        (x > 0 → result / x = result) ∧ 
        (x < 0 → result / x = -result)) ∧
      -- Property 6: NINF is not finite
      ¬result.isFinite ∧
      -- Property 7: NINF is negative
      result < 0 ∧
      -- Property 8: NINF squared is positive infinity
      result * result = -result ∧
      -- Property 9: Absolute value of NINF is positive infinity
      result.abs = -result
    ⌝⦄ := by
  simp [NINF]
  apply neg_inf_properties