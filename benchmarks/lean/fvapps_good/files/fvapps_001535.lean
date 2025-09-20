-- <vc-preamble>
def sum_list : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_chef_money (rows: List (List Nat)) : Nat := sorry

theorem chef_money_nonnegative (rows: List (List Nat)) :
  calculate_chef_money rows ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>