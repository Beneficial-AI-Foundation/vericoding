-- <vc-helpers>
-- </vc-helpers>

def splitByValue (k : Int) (elements : List Int) : List Int :=
  sorry

theorem preserves_elements (k : Int) (elements : List Int) :
  let result := splitByValue k elements
  result.length = elements.length ∧
  ∀ x, (result.count x) = (elements.count x) :=
  sorry

theorem correct_partitioning (k : Int) (elements : List Int) :
  let result := splitByValue k elements
  let splitPoint := (List.filter (· < k) result).length
  (List.take splitPoint result).all (· < k) ∧
  (List.drop splitPoint result).all (· ≥ k) :=
  sorry

theorem maintains_relative_order (k : Int) (elements : List Int) :
  let result := splitByValue k elements
  List.filter (· < k) result = List.filter (· < k) elements ∧ 
  List.filter (· ≥ k) result = List.filter (· ≥ k) elements :=
  sorry

/-
info: [4, 6, 10, 10, 6]
-/
-- #guard_msgs in
-- #eval split_by_value 6 [6, 4, 10, 10, 6]

/-
info: [1, 3, 4, 2, 5, 7, 6]
-/
-- #guard_msgs in
-- #eval split_by_value 5 [1, 3, 5, 7, 6, 4, 2]

/-
info: [3, 2, 8, 3, 2, 1]
-/
-- #guard_msgs in
-- #eval split_by_value 1 [3, 2, 8, 3, 2, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded