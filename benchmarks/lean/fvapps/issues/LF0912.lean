-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_lucky_numbers (left right : String) : Nat := sorry

theorem solve_lucky_numbers_range {left right : String} 
  (h1 : ∀ c ∈ left.data, c.isDigit)
  (h2 : ∀ c ∈ right.data, c.isDigit)
  (h3 : left.length > 0)
  (h4 : right.length > 0)
  (h5 : left.toNat? = some (l : Nat))
  (h6 : right.toNat? = some (r : Nat))
  (h7 : l ≤ 10^9)
  (h8 : r ≤ 10^9)
  : solve_lucky_numbers left right ≤ 10^9 + 7 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_lucky_numbers_identical_input {n : String}
  (h1 : ∀ c ∈ n.data, c.isDigit) 
  (h2 : n.length > 0)
  (h3 : n.toNat? = some (num : Nat))
  (h4 : num ≤ 10^9)
  : solve_lucky_numbers n n ≤ 1 := sorry

theorem solve_lucky_numbers_invalid_input_left {n right : String}
  (h1 : ∃ c ∈ n.data, !c.isDigit)
  (h2 : ∀ c ∈ right.data, c.isDigit)
  : solve_lucky_numbers n right = 0 := sorry

theorem solve_lucky_numbers_invalid_input_right {left n : String}
  (h1 : ∀ c ∈ left.data, c.isDigit)
  (h2 : ∃ c ∈ n.data, !c.isDigit)
  : solve_lucky_numbers left n = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_lucky_numbers "1" "100"

/-
info: 16
-/
-- #guard_msgs in
-- #eval solve_lucky_numbers "1" "10000"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_lucky_numbers "4444" "4447"
-- </vc-theorems>