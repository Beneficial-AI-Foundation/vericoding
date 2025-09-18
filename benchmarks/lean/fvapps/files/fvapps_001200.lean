-- <vc-preamble>
def check_divisible_by_five : String → Nat
  | s => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def contains_five_or_zero (s : String) : Bool :=
  s.contains '0' || s.contains '5'
-- </vc-definitions>

-- <vc-theorems>
theorem check_divisible_outputs_zero_or_one (s : String) :
  (check_divisible_by_five s = 0) ∨ (check_divisible_by_five s = 1) := sorry

theorem check_divisible_leading_zero (s : String) :
  check_divisible_by_five ("0" ++ s) = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval check_divisible_by_five "19"

/-
info: 1
-/
-- #guard_msgs in
-- #eval check_divisible_by_five "385"

/-
info: 0
-/
-- #guard_msgs in
-- #eval check_divisible_by_five "1234"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible