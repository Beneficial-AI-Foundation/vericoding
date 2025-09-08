/-
In a list of songs, the i-th song has a duration of time[i] seconds. 
Return the number of pairs of songs for which their total duration in seconds is divisible by 60.  Formally, we want the number of indices i, j such that i < j with (time[i] + time[j]) % 60 == 0.

Example 1:
Input: [30,20,150,100,40]
Output: 3
Explanation: Three pairs have a total duration divisible by 60:
(time[0] = 30, time[2] = 150): total duration 180
(time[1] = 20, time[3] = 100): total duration 120
(time[1] = 20, time[4] = 40): total duration 60

Example 2:
Input: [60,60,60]
Output: 3
Explanation: All three pairs have a total duration of 120, which is divisible by 60.

Note:

1 <= time.length <= 60000
1 <= time[i] <= 500
-/

-- <vc-helpers>
-- </vc-helpers>

def num_pairs_divisible_by_60 (times: List Nat) : Nat :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible