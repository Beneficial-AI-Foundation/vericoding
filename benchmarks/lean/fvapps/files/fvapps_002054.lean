-- <vc-preamble>
def sum_list : List Nat → Nat
  | [] => 0
  | x::xs => x + sum_list xs

def list_sum_of_largest (arr : List Nat) (n : Nat) : Nat :=
  sum_list ((List.toArray arr |>.qsort (· ≥ ·) |>.toList).take n)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_fun_factor (n d m : Nat) (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_above_m (n d : Nat) (arr : List Nat)
  (h1 : 0 < n ∧ n ≤ 100)
  (h2 : 0 < d ∧ d ≤ 10)
  (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, x < 1000) :
  find_max_fun_factor n d 1000 arr = list_sum_of_largest arr n :=
sorry

theorem single_element (n d m : Nat) (arr : List Nat)
  (h1 : 0 < n ∧ n ≤ 100)
  (h2 : 0 < d ∧ d ≤ 10)
  (h3 : 0 ≤ m ∧ m ≤ 100)
  (h4 : arr.length = n)
  (h5 : ∀ x ∈ arr, x = 0) :
  find_max_fun_factor n d m arr = 0 :=
sorry
-- </vc-theorems>