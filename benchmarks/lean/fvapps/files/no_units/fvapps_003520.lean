-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sorter (texts : List String) : List String := sorry 

theorem sorter_maintains_length (texts : List String) : 
  List.length (sorter texts) = List.length texts := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorter_same_elements (texts : List String) :
  ∀ x, x ∈ sorter texts ↔ x ∈ texts := sorry

theorem sorter_case_insensitive_sorted (texts : List String) (i : Nat) :
  i < (sorter texts).length - 1 →
  String.toLower ((sorter texts).get! i) ≤ String.toLower ((sorter texts).get! (i+1)) := sorry

theorem sorter_empty : sorter [] = [] := sorry
-- </vc-theorems>