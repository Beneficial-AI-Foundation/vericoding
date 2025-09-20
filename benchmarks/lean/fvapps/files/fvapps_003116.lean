-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_type (a b result : Float) : String := sorry

theorem calc_type_addition (a b : Float) :
  a + b ≠ a - b →
  a + b ≠ a * b →
  a + b ≠ a / b →
  calc_type a b (a + b) = "addition" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_type_subtraction (a b : Float) :
  a - b ≠ a + b →
  a - b ≠ a * b →
  a - b ≠ a / b →
  calc_type a b (a - b) = "subtraction" := sorry

theorem calc_type_multiplication (a b : Float) :
  a * b ≠ a + b →
  a * b ≠ a - b →
  a * b ≠ a / b →
  calc_type a b (a * b) = "multiplication" := sorry

theorem calc_type_division (a b : Float) :
  b ≠ 0 →
  a / b ≠ a + b →
  a / b ≠ a - b →
  a / b ≠ a * b →
  calc_type a b (a / b) = "division" := sorry

theorem calc_type_all_different (a b : Float) (h : b ≠ 0) :
  a + b ≠ a - b →
  a + b ≠ a * b →
  a + b ≠ a / b →
  a - b ≠ a * b →
  a - b ≠ a / b →
  a * b ≠ a / b → 
  ∃ op, calc_type a b op ∈ ["addition", "subtraction", "multiplication", "division"] ∧
  ∀ op', calc_type a b op' ∈ ["addition", "subtraction", "multiplication", "division"] → op' = op := sorry
-- </vc-theorems>