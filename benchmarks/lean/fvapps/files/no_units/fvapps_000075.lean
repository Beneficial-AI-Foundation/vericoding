-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_polygon_beauty (n : Nat) : Bool := sorry

theorem check_polygon_beauty_bool (n : Nat) :
  n > 0 → check_polygon_beauty n = true ∨ check_polygon_beauty n = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_polygon_beauty_iff_div4 (n : Nat) :
  n > 0 → (check_polygon_beauty n = true ↔ n % 4 = 0) := sorry

theorem multiples_of_4_are_beautiful (n : Nat) :
  n > 0 → n % 4 = 0 → check_polygon_beauty n = true := sorry

theorem non_multiples_of_4_not_beautiful (n : Nat) :
  n > 0 → n % 4 ≠ 0 → check_polygon_beauty n = false := sorry
-- </vc-theorems>