-- <vc-preamble>
def matrixAddition {n : Nat} (A B : Matrix Int n) : Matrix Int n :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zeroMatrix (n : Nat) : Matrix Int n :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matrixAddition_commutativity {n : Nat} (A B : Matrix Int n) :
  ∀ i j, i < n → j < n →
    (matrixAddition A B).data[i]!.get! j = (matrixAddition B A).data[i]!.get! j := by
  sorry

theorem matrixAddition_correctness {n : Nat} (A B : Matrix Int n) :
  ∀ i j, i < n → j < n →
    (matrixAddition A B).data[i]!.get! j = A.data[i]!.get! j + B.data[i]!.get! j := by
  sorry

theorem matrixAddition_identity {n : Nat} (A : Matrix Int n) :
  matrixAddition A (zeroMatrix n) = A := by
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval matrix_addition #[[1, 2, 3], [3, 2, 1], [1, 1, 1]] #[[2, 2, 1], [3, 2, 3], [1, 1, 3]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval matrix_addition #[[1, 2], [1, 2]] #[[2, 3], [2, 3]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval matrix_addition #[[1]] #[[2]]
-- </vc-theorems>