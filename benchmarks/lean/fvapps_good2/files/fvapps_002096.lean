-- <vc-preamble>
def list_maximum (nums : List Nat) : Nat :=
  match nums with
  | [] => 0
  | (x::xs) => List.foldl Nat.max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_remainder (nums : List Nat) : Nat := sorry

def list_sort (nums : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_remainder_nonnegative (nums : List Nat) (h : nums ≠ []) :
  find_max_remainder nums ≥ 0 :=
sorry

theorem find_max_remainder_less_than_max (nums : List Nat) (h : nums ≠ []) :
  find_max_remainder nums < list_maximum nums :=
sorry

theorem find_max_remainder_order_independent (nums : List Nat) (h : nums ≠ []) :
  find_max_remainder nums = find_max_remainder (list_sort nums) :=
sorry

theorem find_max_remainder_duplicates_independent (nums : List Nat) (h : nums ≠ []) :
  find_max_remainder nums = find_max_remainder (nums.eraseDups) :=
sorry

theorem find_max_remainder_all_same (n : Nat) (nums : List Nat)
  (h : nums = List.replicate (List.length nums) n) :
  find_max_remainder nums = 0 :=
sorry
-- </vc-theorems>