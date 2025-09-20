-- <vc-preamble>
def sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => h + sum t

def minimum (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | h::t => min h (minimum t)

def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => max h (maximum t)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_min_cost (n : Nat) (arr : List Nat) (m : Nat) (offers : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_min_cost_bounded_by_sum 
  (n : Nat) (arr : List Nat) (m : Nat) (offers : List (List Nat)) :
  calculate_min_cost n arr m offers ≤ sum arr :=
  sorry

theorem calculate_min_cost_nonnegative 
  (n : Nat) (arr : List Nat) (m : Nat) (offers : List (List Nat)) :
  calculate_min_cost n arr m offers ≥ 0 :=
  sorry

theorem calculate_min_cost_singleton 
  (arr : List Nat) (m : Nat) (offers : List (List Nat)) :
  arr.length = 1 → calculate_min_cost 1 arr m offers = arr.head! :=
  sorry

theorem calculate_min_cost_pair_with_offer
  (arr : List Nat) (m : Nat) (offers : List (List Nat)) :
  arr.length = 2 → 
  (∃ o ∈ offers, o.head! = 2) → 
  calculate_min_cost 2 arr m offers ≤ sum arr ∧ 
  calculate_min_cost 2 arr m offers ≥ maximum arr :=
  sorry

theorem calculate_min_cost_four_items_with_max_discounts
  (arr : List Nat) :
  arr.length = 4 →
  let offers := [[2,1,2], [2,3,4], [3,1,2,3], [4,1,2,3,4]]
  let m := offers.length
  calculate_min_cost 4 arr m offers ≤ sum arr - minimum arr :=
  sorry

theorem calculate_min_cost_monotonicity
  (arr : List Nat) :
  let n := arr.length
  let offers := [[n] ++ (List.range n).map (fun x => x + 1)]
  let m := 1
  calculate_min_cost n arr m offers ≤ sum arr :=
  sorry
-- </vc-theorems>