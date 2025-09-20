-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_array {α : Type} (arr1 : List α) (arr2 : List Nat) : List α := sorry 

theorem find_array_length_bound {α : Type} (arr1 : List α) (arr2 : List Nat) :
  List.length (find_array arr1 arr2) ≤ min (List.length arr1) (List.length arr2) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_array_elements_from_arr1 {α : Type} (arr1 : List α) (arr2 : List Nat) :
  ∀ x ∈ find_array arr1 arr2, x ∈ arr1 := sorry

theorem find_array_matches_valid_indexes {α : Type} (arr1 : List α) (arr2 : List Nat) :
  find_array arr1 arr2 = arr2.filterMap (fun i => if h : i < arr1.length then some (arr1.get ⟨i, h⟩) else none) := sorry

theorem find_array_empty {α : Type} :
  find_array ([] : List α) ([] : List Nat) = [] ∧
  ∀ (l : List α), find_array l [] = [] ∧
  ∀ (l : List Nat), find_array ([] : List α) l = [] := sorry

theorem find_array_non_empty {α : Type} (arr1 : List α) (arr2 : List Nat) (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  ∀ (i : Nat) (x : α) (h : i < arr1.length), 
    i ∈ arr2 → 
    x = arr1.get ⟨i, h⟩ →
    x ∈ find_array arr1 arr2 := sorry
-- </vc-theorems>