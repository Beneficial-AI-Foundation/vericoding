-- <vc-preamble>
def split_array_same_average (arr : List Int) : Bool :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_list (l : List Int) : Int :=
l.foldl (· + ·) 0
-- </vc-definitions>

-- <vc-theorems>
theorem split_array_verification {arr : List Int} 
  (h : split_array_same_average arr = true) 
  (h1 : arr.length ≥ 2)
  (h2 : ∀ x ∈ arr, x ≥ 0 ∧ x ≤ 100) :
  ∃ (subset1 subset2 : List Int),
    subset1 ≠ [] ∧ 
    subset2 ≠ [] ∧
    (∀ x, x ∈ subset1 ∨ x ∈ subset2 ↔ x ∈ arr) ∧
    (sum_list subset1) * subset2.length = (sum_list subset2) * subset1.length :=
sorry

theorem single_element_false {x : Int} (h : x ≥ 1 ∧ x ≤ 10) :
  split_array_same_average [x] = false :=
sorry

theorem identical_elements_splittable {x : Int} {n : Nat}
  (h : n ≥ 2) :
  split_array_same_average (List.replicate n x) = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval split_array_same_average [1, 2, 3, 4, 5, 6, 7, 8]

/-
info: True
-/
-- #guard_msgs in
-- #eval split_array_same_average [1, 2, 3]

/-
info: True
-/
-- #guard_msgs in
-- #eval split_array_same_average [3, 1, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded