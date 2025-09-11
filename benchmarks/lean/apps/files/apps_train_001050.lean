-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_ops_to_zeros (s : String) : Nat := sorry

theorem output_bounds (s : String) :
  let result := min_ops_to_zeros s
  0 ≤ result ∧ result ≤ s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string :
  min_ops_to_zeros "" = 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_ops_to_zeros "01001001"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_ops_to_zeros "0"

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_ops_to_zeros "11"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible