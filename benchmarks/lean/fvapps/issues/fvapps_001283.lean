-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + List.sum xs

def min_in_list : List Nat → Nat → Nat
  | [], default => default
  | [x], _ => x
  | x::xs, default => min x (min_in_list xs default)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_meal_sets (n m : Nat) (costs : List Nat) (meal_sets : List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_meal_sets_basic_properties 
  (n : Nat) (costs : List Nat) (meal_costs : List Nat) :
  n > 0 → n ≤ 5 →
  ∀ c ∈ costs, c > 0 ∧ c ≤ 100 →
  ∀ mc ∈ meal_costs, mc > 0 ∧ mc ≤ 200 →
  costs.length = n →
  let m := meal_costs.length
  let meal_sets := sorry -- construction of meal sets
  let result := solve_meal_sets n m costs meal_sets 
  result > 0 ∧ result ≤ List.sum costs := by
  sorry

theorem solve_meal_sets_bounded_by_min
  (n : Nat) (costs : List Nat) (meal_costs : List Nat) :
  n > 0 → n ≤ 5 →
  ∀ c ∈ costs, c > 0 ∧ c ≤ 100 →
  ∀ mc ∈ meal_costs, mc > 0 ∧ mc ≤ 200 →
  costs.length = n →
  let m := meal_costs.length
  let meal_sets := sorry -- construction of meal sets  
  let result := solve_meal_sets n m costs meal_sets
  result ≤ min (List.sum costs) (min_in_list meal_costs (List.sum costs)) := by
  sorry

theorem solve_meal_sets_empty_meals
  (costs : List Nat) :
  costs = [4, 5] →
  solve_meal_sets 2 0 costs [] = 9 := by
  sorry

theorem solve_meal_sets_single_optimal_meal
  (costs : List Nat) (meal_sets : List (List Nat)) :
  costs = [10] →
  meal_sets = [[5, 1, 1]] →
  solve_meal_sets 1 1 costs meal_sets = 5 := by
  sorry

theorem solve_meal_sets_two_items_optimal_meal
  (costs : List Nat) (meal_sets : List (List Nat)) :
  costs = [10, 10] →
  meal_sets = [[15, 2, 1, 2]] →
  solve_meal_sets 2 1 costs meal_sets = 15 := by
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_meal_sets 3 3 [3, 5, 6] [[11, 3, 1, 2, 3], [5, 2, 1, 2], [5, 2, 1, 3]]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_meal_sets 2 1 [4, 5] [[7, 2, 1, 2]]

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_meal_sets 1 1 [10] [[8, 1, 1]]
-- </vc-theorems>