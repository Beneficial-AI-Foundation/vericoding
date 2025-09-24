-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def differentiate (p : Polynomial) (x : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem differentiate_return_number 
  (p : Polynomial) (x : Int) : 
  ∃ n : Int, differentiate p x = n :=
  sorry

theorem differentiate_constant
  (n : Int) (x : Int) :
  differentiate (Polynomial.const n) x = 0 :=
  sorry

theorem differentiate_linear_constant_derivative 
  (p : Polynomial) (x₁ x₂ : Int)
  (h : ∀ term : Polynomial, term ≠ Polynomial.var → false) :
  differentiate p x₁ = differentiate p x₂ := 
  sorry

theorem differentiate_var
  (x : Int) :
  differentiate Polynomial.var x = 1 :=
  sorry

theorem differentiate_square
  (x : Int) :
  differentiate (Polynomial.power 1 2) x = 2 * x :=
  sorry

theorem differentiate_constant_zero
  (n : Int) (x : Int) :
  differentiate (Polynomial.const n) x = 0 :=
  sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval differentiate "12x+2" 3

/-
info: 9
-/
-- #guard_msgs in
-- #eval differentiate "x^2+3x+2" 3

/-
info: -20
-/
-- #guard_msgs in
-- #eval differentiate "-5x^2+10x+4" 3
-- </vc-theorems>