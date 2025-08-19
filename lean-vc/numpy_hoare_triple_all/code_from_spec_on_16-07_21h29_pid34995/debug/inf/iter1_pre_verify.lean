import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.inf",
  "category": "Special float values",
  "description": "IEEE 754 floating point representation of (positive) infinity",
  "url": "https://numpy.org/doc/stable/reference/constants.html#numpy.inf",
  "doc": "IEEE 754 floating point representation of (positive) infinity.\n\nUse inf because Inf, Infinity, PINF and infty are aliases for inf. For more details, see inf.\n\nSee Also:\ninf",
  "code": "# Defined in umathmodule.c\nnumpy.inf = float('inf')\n# Aliases: Inf, Infinity, PINF, infty"
}
-/

open Std.Do

/-- IEEE 754 floating point representation of (positive) infinity -/
def inf : Id Float :=
  pure (1.0 / 0.0)

-- LLM HELPER
lemma inf_is_pos_inf : inf.run = 1.0 / 0.0 := by
  rfl

-- LLM HELPER
lemma pos_inf_properties (x : Float) : 
  let pinf := (1.0 : Float) / 0.0
  (Float.isFinite x → pinf > x) ∧
  (Float.isFinite x → pinf + x = pinf) ∧
  (Float.isFinite x ∧ x > 0 → pinf * x = pinf) ∧
  (Float.isFinite x ∧ x < 0 → pinf * x = -pinf) ∧
  (Float.isFinite x ∧ x ≠ 0 → (x > 0 → pinf / x = pinf) ∧ (x < 0 → pinf / x = -pinf)) ∧
  ¬Float.isFinite pinf ∧
  pinf > 0 := by
  constructor
  · intro h
    exact Float.lt_pos_inf_of_isFinite h
  constructor
  · intro h
    exact Float.add_pos_inf_of_isFinite h
  constructor
  · intro ⟨h1, h2⟩
    exact Float.mul_pos_inf_of_isFinite_pos h1 h2
  constructor
  · intro ⟨h1, h2⟩
    exact Float.mul_pos_inf_of_isFinite_neg h1 h2
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · intro h3
      exact Float.div_pos_inf_of_isFinite_pos h1 h3
    · intro h3
      exact Float.div_pos_inf_of_isFinite_neg h1 h3
  constructor
  · exact Float.not_isFinite_pos_inf
  · exact Float.zero_lt_pos_inf

/-- Specification: inf represents positive infinity with the following properties:
    1. inf is greater than any finite float value
    2. inf + any finite value = inf
    3. inf * positive finite value = inf
    4. inf * negative finite value = -inf
    5. inf / any finite non-zero value = inf (with appropriate sign) -/
theorem inf_spec :
    ⦃⌜True⌝⦄
    inf
    ⦃⇓result => ⌜
      -- Property 1: inf is greater than all finite values
      (∀ x : Float, Float.isFinite x → result > x) ∧
      -- Property 2: inf + finite = inf
      (∀ x : Float, Float.isFinite x → result + x = result) ∧
      -- Property 3: inf * positive finite = inf
      (∀ x : Float, Float.isFinite x ∧ x > 0 → result * x = result) ∧
      -- Property 4: inf * negative finite = -inf
      (∀ x : Float, Float.isFinite x ∧ x < 0 → result * x = -result) ∧
      -- Property 5: inf / finite non-zero = inf (with sign)
      (∀ x : Float, Float.isFinite x ∧ x ≠ 0 → 
        (x > 0 → result / x = result) ∧ 
        (x < 0 → result / x = -result)) ∧
      -- Property 6: inf is not finite
      ¬Float.isFinite result ∧
      -- Property 7: inf is positive
      result > 0
    ⌝⦄ := by
  simp [inf]
  rw [Id.spec_pure]
  simp [inf_is_pos_inf]
  exact pos_inf_properties