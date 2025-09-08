/-
Christmas is coming, and Santa has a long list to go through, to find who deserves presents for the big day. Go through a list of children, and return a list containing every child who appeared on Santa's list. Do not add any child more than once. Output should be sorted.
~~~if:java
For java, use Lists.
~~~

Comparison should be case sensitive and the returned list should contain only one copy of each name: `"Sam"` and `"sam"` are different, but `"sAm"` and `"sAm"` are not.
-/

-- <vc-helpers>
-- </vc-helpers>

def find_children (santas_list : List String) (children : List String) : List String := sorry

def isSorted (xs : List String) : Prop :=
  ∀ i j, i < j → j < xs.length → xs[i]! ≤ xs[j]!

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

/-
info: ['Jason', 'Jordan']
-/
-- #guard_msgs in
-- #eval find_children ["Jason", "Jackson", "Jordan", "Johnny"] ["Jason", "Jordan", "Jennifer"]

/-
info: ['JJ', 'Jason']
-/
-- #guard_msgs in
-- #eval find_children ["Jason", "Jackson", "Johnson", "JJ"] ["Jason", "James", "JJ"]

/-
info: ['JAsoN', 'jASon']
-/
-- #guard_msgs in
-- #eval find_children ["jASon", "JAsoN", "JaSON", "jasON"] ["JasoN", "jASOn", "JAsoN", "jASon", "JASON"]

-- Apps difficulty: introductory
-- Assurance level: unguarded