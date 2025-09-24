-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_children (santas_list : List String) (children : List String) : List String := sorry

def isSorted (xs : List String) : Prop :=
  ∀ i j, i < j → j < xs.length → xs[i]! ≤ xs[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem find_children_sorted (santas_list children : List String) :
  let result := find_children santas_list children
  isSorted result := sorry

theorem find_children_subset (santas_list children : List String) :
  let result := find_children santas_list children
  (∀ x ∈ result, x ∈ santas_list ∧ x ∈ children) := sorry

theorem find_children_complete_intersection (santas_list children : List String) :
  let result := find_children santas_list children
  ∀ x, (x ∈ santas_list ∧ x ∈ children) → x ∈ result := sorry

theorem find_children_no_duplicates (santas_list children : List String) :
  let result := find_children santas_list children
  ∀ i j, i < j → j < result.length → result[i]! ≠ result[j]! := sorry

theorem find_children_identity (names : List String) :
  let result := find_children names names
  (∀ x ∈ result, x ∈ names) ∧
  (∀ x ∈ names, x ∈ result) ∧
  isSorted result := sorry

theorem find_children_symmetry (list1 list2 : List String) :
  find_children list1 list2 = find_children list2 list1 := sorry

theorem find_children_empty (names : List String) :
  find_children names [] = [] ∧
  find_children [] names = [] := sorry
-- </vc-theorems>