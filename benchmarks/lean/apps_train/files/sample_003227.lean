/-
Write a function that accepts two square matrices (`N x N` two dimensional arrays), and return the sum of the two. Both matrices being passed into the function will be of size `N x N` (square), containing only integers.

How to sum two matrices:

Take each cell `[n][m]` from the first matrix, and add it with the same `[n][m]` cell from the second matrix. This will be cell `[n][m]` of the solution matrix.

Visualization: 
```
|1 2 3|     |2 2 1|     |1+2 2+2 3+1|     |3 4 4|
|3 2 1|  +  |3 2 3|  =  |3+3 2+2 1+3|  =  |6 4 4|
|1 1 1|     |1 1 3|     |1+1 1+1 1+3|     |2 2 4|
```

## Example
-/

def matrixAddition {n : Nat} (A B : Matrix Int n) : Matrix Int n :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def zeroMatrix (n : Nat) : Matrix Int n :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded