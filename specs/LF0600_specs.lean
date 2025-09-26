-- <vc-preamble>
def find_max_shares_to_sell (shares: List Share) : Nat :=
  sorry

def is_unique_shares (shares: List Share) : Bool :=
  sorry

def is_strictly_increasing (l: List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => x < y && is_strictly_increasing (y :: xs)

def is_strictly_decreasing (l: List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => x > y && is_strictly_decreasing (y :: xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sorted_shares (shares: List Share) : List Share :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_shares_bounds {shares: List Share} (h: shares ≠ []) :
  1 ≤ find_max_shares_to_sell shares ∧ find_max_shares_to_sell shares ≤ shares.length :=
sorry

theorem max_shares_sort_invariant (shares: List Share) :
  find_max_shares_to_sell shares = find_max_shares_to_sell (sorted_shares shares) :=
sorry

theorem strictly_increasing_max_shares {shares: List Share} (h1: shares ≠ []) 
  (h2: is_strictly_increasing (shares.map Share.value)) :
  find_max_shares_to_sell (sorted_shares shares) = shares.length :=
sorry

theorem strictly_decreasing_max_shares {shares: List Share} (h1: shares ≠ [])
  (h2: is_strictly_decreasing (shares.map Share.value)) :
  find_max_shares_to_sell (sorted_shares shares) = 1 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_shares_to_sell [[1, 2], [4, 3], [3, 5], [2, 4]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_shares_to_sell [[1, 2], [2, 3], [3, 4]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_shares_to_sell [[5, 1], [4, 2], [3, 3], [2, 4], [1, 5]]
-- </vc-theorems>