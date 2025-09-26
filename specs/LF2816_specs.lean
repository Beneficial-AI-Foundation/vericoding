-- <vc-preamble>
def sumDifferencesBetweenProductsAndLCMs (pairs : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + List.sum t
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_gives_zero :
  sumDifferencesBetweenProductsAndLCMs [] = 0 :=
sorry

theorem zero_pairs_give_zero (n : Nat) :
  sumDifferencesBetweenProductsAndLCMs (List.replicate n (0, 0)) = 0 :=
sorry

theorem result_leq_sum_products (pairs : List (Nat × Nat)) :
  pairs ≠ [] →
  sumDifferencesBetweenProductsAndLCMs pairs ≤ 
    List.sum (pairs.map (fun p => p.fst * p.snd)) :=
sorry

theorem commutative (pairs : List (Nat × Nat)) :
  sumDifferencesBetweenProductsAndLCMs pairs = 
  sumDifferencesBetweenProductsAndLCMs (pairs.map fun p => (p.snd, p.fst)) :=
sorry

/-
info: 840
-/
-- #guard_msgs in
-- #eval sum_differences_between_products_and_LCMs [[15, 18], [4, 5], [12, 60]]

/-
info: 1092
-/
-- #guard_msgs in
-- #eval sum_differences_between_products_and_LCMs [[1, 1], [0, 0], [13, 91]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_differences_between_products_and_LCMs []
-- </vc-theorems>