-- <vc-preamble>
def sumList (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => h + sumList t

def zipWithIndex {α : Type} (l : List α) : List (Nat × α) :=
  let rec aux (i : Nat) (xs : List α) : List (Nat × α) :=
    match xs with
    | [] => []
    | h :: t => (i, h) :: aux (i+1) t
  aux 0 l
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def knapsack (capacity : Nat) (items : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem knapsack_result_length_matches_input
    (capacity : Nat) (items : List (Nat × Nat)) :
    (knapsack capacity items).length = items.length :=
sorry

theorem knapsack_result_nonnegative
    (capacity : Nat) (items : List (Nat × Nat)) :
    ∀ x ∈ knapsack capacity items, x ≥ 0 :=
sorry

theorem knapsack_total_size_within_capacity
    (capacity : Nat) (items : List (Nat × Nat)) :
    let result := knapsack capacity items
    let sizes := List.map (fun p => (items[p.1]!).1 * p.2) (zipWithIndex result)
    sumList sizes ≤ capacity :=
sorry

theorem knapsack_optimal_ratio
    (capacity : Nat) (items : List (Nat × Nat)) (i : Nat) :
    i < items.length →
    let result := knapsack capacity items
    let sizes := List.map (fun p => (items[p.1]!).1 * p.2) (zipWithIndex result)
    let total_size := sumList sizes
    let ratio := items[i]!.2 / items[i]!.1
    items[i]!.1 + total_size ≤ capacity →
    ∀ j < items.length,
      items[j]!.2 / items[j]!.1 = 0 ∨ items[j]!.2 / items[j]!.1 < ratio :=
sorry

theorem knapsack_zero_capacity
    (items : List (Nat × Nat)) :
    knapsack 0 items = List.replicate items.length 0 :=
sorry

theorem knapsack_empty_items
    (capacity : Nat) :
    knapsack capacity [] = [] :=
sorry
-- </vc-theorems>