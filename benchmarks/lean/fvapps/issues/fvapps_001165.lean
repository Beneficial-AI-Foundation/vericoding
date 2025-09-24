-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_binary_string_flips : BinaryString → Nat
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_string_has_no_pairs (b : Bool) : 
  solve_binary_string_flips (BinaryString.cons b BinaryString.empty) = 0 := by
  sorry

theorem output_is_nonnegative (s : BinaryString) : 
  solve_binary_string_flips s ≥ 0 := by
  sorry

theorem empty_string_returns_zero :
  solve_binary_string_flips BinaryString.empty = 0 := by
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_binary_string_flips "001"

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_binary_string_flips "0"

/-
info: 18
-/
-- #guard_msgs in
-- #eval solve_binary_string_flips "1111"
-- </vc-theorems>