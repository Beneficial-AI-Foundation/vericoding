-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_binary_substrings (s : String) : Nat := sorry

theorem solve_returns_nat (s : String) :
  solve_binary_substrings s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_ge_ones_count (s : String) :
  (∃ c ∈ s.toList, c = '1') →
  solve_binary_substrings s ≥ (s.toList.filter (· = '1')).length := sorry

theorem power_two_string_bounds (n : Nat) :
  n > 0 →
  let s := String.mk ('1'::List.replicate n '0')
  solve_binary_substrings s ≥ 1 ∧
  solve_binary_substrings s ≤ n + 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_binary_substrings "0110"

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_binary_substrings "0101"

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_binary_substrings "00001000"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible