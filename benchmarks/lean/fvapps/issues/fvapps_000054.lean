-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_win (nums : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_win_large_numbers_filtered {nums : List Nat} :
  can_win nums = can_win (nums.filter (· < 2049)) :=
  sorry

theorem can_win_sum_condition {nums : List Nat} :
  can_win nums = ((nums.filter (· < 2049)).foldl (· + ·) 0 ≥ 2048) :=
  sorry

theorem can_win_large_number_ignored {n : Nat} (h : n ≥ 2049) : 
  can_win [n] = false :=
  sorry

theorem can_win_large_with_2048 {n : Nat} (h : n ≥ 2049) :
  can_win [n, 2048] = true :=
  sorry

theorem can_win_small_numbers_sum {nums : List Nat}
  (h : ∀ n ∈ nums, n ≤ 2047) :
  can_win nums = (nums.foldl (· + ·) 0 ≥ 2048) :=
  sorry

end GameTheory

/-
info: True
-/
-- #guard_msgs in
-- #eval can_win [1024, 512, 64, 512]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_win [64, 512, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_win [2048, 4096]
-- </vc-theorems>