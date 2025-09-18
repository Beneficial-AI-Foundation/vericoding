-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_triangle (a b c : Int) : Bool := sorry

theorem non_positive_sides_are_invalid {a b c : Int} :
  (a ≤ 0 ∨ b ≤ 0 ∨ c ≤ 0) → is_triangle a b c = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangle_inequality {a b c : Int} : 
  is_triangle a b c = true → 
  (a < b + c ∧ b < a + c ∧ c < a + b) := sorry

theorem equilateral_triangle {side : Int} :
  side > 0 → is_triangle side side side = true := sorry
-- </vc-theorems>