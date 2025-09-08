/-
You have to create a method "compoundArray" which should take as input two int arrays of different length and return one int array with numbers of both arrays shuffled one by one. 
```Example: 
Input - {1,2,3,4,5,6} and {9,8,7,6} 
Output - {1,9,2,8,3,7,4,6,5,6}
```
-/

-- <vc-helpers>
-- </vc-helpers>

def compound_array {α : Type} [DecidableEq α] (a b : List α) : List α := sorry

theorem compound_array_length {α : Type} [DecidableEq α] (a b : List α) :
  (compound_array a b).length = a.length + b.length := sorry

theorem compound_array_preserves_elements {α : Type} [DecidableEq α] (a b : List α) (x : α) :
  (x ∈ a ∨ x ∈ b) ↔ x ∈ compound_array a b := sorry

theorem compound_array_maintains_relative_order {α : Type} [DecidableEq α] (a b : List α) :
  ∀ i j x y, i < j →
    ((x ∈ a ∧ y ∈ a) → 
      (List.get (compound_array a b) i = x ∧ List.get (compound_array a b) j = y) → 
      ∃ i' j', List.get a i' = x ∧ List.get a j' = y ∧ i' < j') ∧
    ((x ∈ b ∧ y ∈ b) → 
      (List.get (compound_array a b) i = x ∧ List.get (compound_array a b) j = y) → 
      ∃ i' j', List.get b i' = x ∧ List.get b j' = y ∧ i' < j') := sorry

theorem compound_array_empty_list {α : Type} [DecidableEq α] (a : List α) :
  compound_array a [] = a ∧ 
  compound_array [] a = a := sorry

theorem compound_array_empty_both {α : Type} [DecidableEq α] :
  compound_array ([] : List α) [] = [] := sorry

/-
info: [1, 9, 2, 8, 3, 7, 4, 6, 5, 6]
-/
-- #guard_msgs in
-- #eval compound_array [1, 2, 3, 4, 5, 6] [9, 8, 7, 6]

/-
info: [11, 21, 12, 22, 23, 24]
-/
-- #guard_msgs in
-- #eval compound_array [11, 12] [21, 22, 23, 24]

/-
info: []
-/
-- #guard_msgs in
-- #eval compound_array [] []

-- Apps difficulty: introductory
-- Assurance level: guarded