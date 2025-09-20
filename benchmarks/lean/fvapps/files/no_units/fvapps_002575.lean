-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def yes_no (arr : List α) : List α := sorry

theorem yes_no_length_preserved {α : Type} (arr : List α) : 
  List.length (yes_no arr) = List.length arr := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem yes_no_first_element_preserved {α : Type} [Inhabited α] (arr : List α) :
  arr ≠ [] → List.head! (yes_no arr) = List.head! arr := sorry

theorem yes_no_small_lists {α : Type} [Inhabited α] (arr : List α) :
  (List.length arr ≤ 1 → yes_no arr = arr) ∧
  (List.length arr = 2 → 
    List.get! (yes_no arr) 0 = List.get! arr 0 ∧
    List.get! (yes_no arr) 1 = List.get! arr 1) := sorry

theorem yes_no_homogeneous_type {α : Type} (arr : List α) :
  List.length (yes_no arr) = List.length arr := sorry
-- </vc-theorems>