-- <vc-preamble>
def sum_subarray_mins (nums : List Nat) : Nat :=
  sorry

def list_min (l : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_max (l : List Nat) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_subarray_mins_non_negative (nums : List Nat) :
  sum_subarray_mins nums ≥ 0 := sorry

theorem sum_subarray_mins_modulo_bound (nums : List Nat) :
  sum_subarray_mins nums < 10^9 + 7 := sorry

theorem sum_subarray_mins_singleton (n : Nat) :
  sum_subarray_mins [n] = n := sorry

theorem sum_subarray_mins_min_bound {nums : List Nat} (h : nums.length ≥ 2) :
  sum_subarray_mins nums ≥ list_min nums := sorry

theorem sum_subarray_mins_append_larger {nums : List Nat} (h : nums.length ≥ 2) :
  let max := list_max nums
  sum_subarray_mins (nums ++ [max + 1]) % (10^9 + 7) ≥ sum_subarray_mins nums % (10^9 + 7) := sorry

/-
info: 17
-/
-- #guard_msgs in
-- #eval sum_subarray_mins [3, 1, 2, 4]

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_subarray_mins [1]

/-
info: 444
-/
-- #guard_msgs in
-- #eval sum_subarray_mins [11, 81, 94, 43, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded