-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_right_triangle (a b c : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_inputs (a b c : Int) :
  a = 0 ∨ b = 0 ∨ c = 0 → check_right_triangle a b c = "NO" :=
  sorry

theorem pythagorean_triples (a b c : Int) :
  a > 0 ∧ b > 0 ∧ c > 0 →
  (a * a = b * b + c * c ∨ b * b = a * a + c * c ∨ c * c = a * a + b * b) →
  check_right_triangle a b c = "YES" :=
  sorry

theorem not_pythagorean_triples (a b c : Int) :
  a > 0 ∧ b > 0 ∧ c > 0 →
  ¬(a * a = b * b + c * c ∨ b * b = a * a + c * c ∨ c * c = a * a + b * b) →
  check_right_triangle a b c = "NO" :=
  sorry

theorem negative_inputs (a b c : Int) :
  a < 0 ∨ b < 0 ∨ c < 0 → check_right_triangle a b c = "NO" :=
  sorry
-- </vc-theorems>