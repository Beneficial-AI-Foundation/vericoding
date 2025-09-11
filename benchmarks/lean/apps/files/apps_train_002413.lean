-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_pairs_divisible_by_60 (times: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_pairs_non_negative (times: List Nat) : 
  num_pairs_divisible_by_60 times ≥ 0 :=
sorry

theorem num_pairs_max_bound (times: List Nat) :
  num_pairs_divisible_by_60 times ≤ (times.length * (times.length - 1)) / 2 :=
sorry

theorem mod_60_preserves_result (times: List Nat) :
  num_pairs_divisible_by_60 times = 
  num_pairs_divisible_by_60 (times.map (λ x => x % 60)) :=
sorry

theorem all_60s_triangular_nums (n: Nat) :
  let times := List.replicate n 60
  num_pairs_divisible_by_60 times = (n * (n-1)) / 2 :=
sorry

theorem complementary_pairs (n: Nat) :
  let times := List.replicate n 20 ++ List.replicate n 40 
  num_pairs_divisible_by_60 times = n * n :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_pairs_divisible_by_60 [30, 20, 150, 100, 40]

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_pairs_divisible_by_60 [60, 60, 60]

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_pairs_divisible_by_60 [20, 40]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible