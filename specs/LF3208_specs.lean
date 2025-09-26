-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def square_free_part (n : Int) : Option Int := sorry

def Real.toInt (x : Float) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_integer_returns_none (x : Float) : 
  square_free_part (Real.toInt x) = none := by sorry

theorem non_positive_returns_none (x : Int) : 
  x ≤ 0 → square_free_part x = none := by sorry

theorem result_divides_input (n : Int) :
  n > 0 → 
  match square_free_part n with
  | some result => result ∣ n 
  | none => True
  := by sorry

theorem no_square_factors (n : Int) :
  n > 0 →
  match square_free_part n with
  | some result => ∀ i : Int, i > 1 → ¬(i * i ∣ result)  
  | none => True
  := by sorry
-- </vc-theorems>