-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_repeated_subarray (A B : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_size_bounds {A B : List Nat} (h1 : A.length > 0) (h2 : B.length > 0) :
  let result := find_max_repeated_subarray A B
  result ≥ 0 ∧ result ≤ min A.length B.length :=
  sorry

theorem identical_arrays {A : List Nat} (h : A.length > 0) :
  find_max_repeated_subarray A A = A.length :=
  sorry

theorem symmetric_property {A B : List Nat} (h1 : A.length > 0) (h2 : B.length > 0) :
  find_max_repeated_subarray A B = find_max_repeated_subarray B A :=
  sorry

theorem disjoint_arrays {A B : List Nat} (h1 : A.length > 0) (h2 : B.length > 0)
  (h3 : ∀ x ∈ B, ∀ y ∈ A, x ≠ y) :
  find_max_repeated_subarray A B = 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_repeated_subarray [1, 2, 3, 2, 1] [3, 2, 1, 4, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_max_repeated_subarray [1, 2, 3] [4, 5, 6]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_repeated_subarray [1, 1, 1] [1, 1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded