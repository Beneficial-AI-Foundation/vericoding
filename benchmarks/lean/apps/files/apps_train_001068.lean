-- <vc-helpers>
-- </vc-helpers>

def solve_kabir_game (n k : Nat) : Nat :=
  sorry

theorem bound_lower : ∀ k, 0 ≤ solve_kabir_game 0 (k+1) :=
  sorry

theorem bound_upper : solve_kabir_game (10^9) (10^9) < 1000000007 :=
  sorry 

theorem result_in_mod_range : ∀ n k, k > 0 → 
  0 ≤ solve_kabir_game n k ∧ solve_kabir_game n k < 1000000007 :=
  sorry

theorem k_affects_result : ∀ n k, k > 1 → 
  solve_kabir_game n k ≠ solve_kabir_game n (k-1) :=
  sorry

theorem small_inputs_bound : ∀ n k,
  n ≤ 1000 → k ≤ 1000 → k > 0 →
  solve_kabir_game n k ≤ (n + k)^2 + k :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_kabir_game 0 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_kabir_game 1 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_kabir_game 1 3

/-
info: 46
-/
-- #guard_msgs in
-- #eval solve_kabir_game 4 6

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible