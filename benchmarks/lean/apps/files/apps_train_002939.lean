-- <vc-helpers>
-- </vc-helpers>

def denumerate (l : List (Int × Char)) : Option String := sorry

theorem denumerate_preserves_mapping (l : List (Int × Char)) :
  match denumerate l with
  | none => True  
  | some result =>
    ∀ (i : Nat), i < result.length →
      ∃ (pair : Int × Char), pair ∈ l ∧ 
        pair.1 = i ∧ result.data[i]! = pair.2
  := sorry

theorem invalid_types_return_none (l : List (Int × Char)) (h : ∀ x ∈ l, ¬(x.2.isAlpha)) :
  denumerate l = none := sorry

theorem gaps_in_sequence_property (l : List (Int × Char)) :
  match denumerate l with 
  | none => True
  | some result =>
    ∀ i j : Nat, i < j → j < result.length →
      ∃ (pair₁ pair₂ : Int × Char), 
        pair₁ ∈ l ∧ pair₂ ∈ l ∧
        pair₁.1 = i ∧ pair₂.1 = j
  := sorry

theorem non_list_inputs_return_none :
  denumerate [] = none := sorry

/-
info: 'monty'
-/
-- #guard_msgs in
-- #eval denumerate [(4, "y"), (1, "o"), (3, "t"), (0, "m"), (2, "n")]

/-
info: False
-/
-- #guard_msgs in
-- #eval denumerate [1]

/-
info: False
-/
-- #guard_msgs in
-- #eval denumerate [(0, "a"), (2, "b")]

-- Apps difficulty: introductory
-- Assurance level: unguarded