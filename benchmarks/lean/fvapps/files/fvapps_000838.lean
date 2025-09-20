-- <vc-preamble>
def list_maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + list_sum xs

def nat_ceil_div (a b : Nat) : Nat :=
  (a + b - 1) / b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_banana_speed (pile_count : Nat) (hours : Nat) (piles : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem edge_cases_singleton_one :
  min_banana_speed 1 1 [1] = 1 :=
sorry

theorem edge_cases_singleton_hundred :
  min_banana_speed 1 1 [100] = 100 :=
sorry

theorem edge_cases_two_ones :
  min_banana_speed 2 2 [1, 1] = 1 :=
sorry
-- </vc-theorems>