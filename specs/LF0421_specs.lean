-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_subarray_mins (nums : List Nat) : Nat :=
  sorry

def list_min (l : List Nat) : Nat :=
  sorry

def list_max (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_subarray_mins_non_negative (nums : List Nat) :
  sum_subarray_mins nums ≥ 0 :=
sorry

theorem sum_subarray_mins_modulo_bound (nums : List Nat) :
  sum_subarray_mins nums < 10^9 + 7 :=
sorry

theorem sum_subarray_mins_singleton (n : Nat) :
  sum_subarray_mins [n] = n :=
sorry

theorem sum_subarray_mins_min_bound {nums : List Nat} (h : nums.length ≥ 2) :
  sum_subarray_mins nums ≥ list_min nums :=
sorry

theorem sum_subarray_mins_append_larger {nums : List Nat} (h : nums.length ≥ 2) :
  let max := list_max nums
  sum_subarray_mins (nums ++ [max + 1]) % (10^9 + 7) ≥ sum_subarray_mins nums % (10^9 + 7) :=
sorry
-- </vc-theorems>