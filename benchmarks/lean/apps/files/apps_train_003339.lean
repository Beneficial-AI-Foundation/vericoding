-- <vc-helpers>
-- </vc-helpers>

def duplicate_elements (xs ys : List Int) : Bool := sorry

-- Symmetry property

theorem duplicate_elements_symmetric (xs ys : List Int) :
  duplicate_elements xs ys = duplicate_elements ys xs := sorry

-- Self duplicates property  

theorem duplicate_elements_self (xs : List Int) :
  xs ≠ [] → duplicate_elements xs xs := sorry

-- Transitivity property

theorem duplicate_elements_transitive (xs ys zs : List Int) :
  duplicate_elements xs ys → 
  duplicate_elements ys zs →
  (∃ n : Int, n ∈ xs ∧ n ∈ ys ∧ n ∈ zs) →
  duplicate_elements xs zs := sorry

-- Superset property

theorem duplicate_elements_superset_left (xs ys : List Int) :
  duplicate_elements xs ys →
  duplicate_elements (xs ++ xs) ys := sorry

theorem duplicate_elements_superset_right (xs ys : List Int) :
  duplicate_elements xs ys →
  duplicate_elements xs (ys ++ ys) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval duplicate_elements [1, 2, 3] [3, 4, 5]

/-
info: False
-/
-- #guard_msgs in
-- #eval duplicate_elements [1, 2, 3] [4, 5, 6]

/-
info: False
-/
-- #guard_msgs in
-- #eval duplicate_elements [] []

-- Apps difficulty: introductory
-- Assurance level: unguarded