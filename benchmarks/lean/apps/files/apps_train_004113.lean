-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseOnDiagonals (matrix : List (List Int)) : List (List Int) := sorry

theorem matrix_size_preservation (n : Nat) : 
  ∀ (matrix : List (List Int)), 
  matrix.length = n → (∀ row ∈ matrix, row.length = n) →
  let result := reverseOnDiagonals matrix
  result.length = n ∧ (∀ row ∈ result, row.length = n) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem main_diagonal_reversal {n : Nat} (matrix : List (List Int))
  (h1 : matrix.length = n) (h2 : ∀ row ∈ matrix, row.length = n) :
  let result := reverseOnDiagonals matrix
  ∀ (i : Fin n), 
  (List.get! (List.get! result i) i) = 
  (List.get! (List.get! matrix (⟨n-1-i, sorry⟩ : Fin n)) (⟨n-1-i, sorry⟩ : Fin n)) := sorry

theorem secondary_diagonal_reversal {n : Nat} (matrix : List (List Int))
  (h1 : matrix.length = n) (h2 : ∀ row ∈ matrix, row.length = n) :
  let result := reverseOnDiagonals matrix
  ∀ (i : Fin n),
  (List.get! (List.get! result i) (⟨n-1-i, sorry⟩ : Fin n)) = 
  (List.get! (List.get! matrix (⟨n-1-i, sorry⟩ : Fin n)) i) := sorry

theorem non_diagonal_elements_unchanged {n : Nat} (matrix : List (List Int))
  (h1 : matrix.length = n) (h2 : ∀ row ∈ matrix, row.length = n) :
  let result := reverseOnDiagonals matrix
  ∀ (i j : Fin n), i ≠ j → i.val ≠ n-1-j.val →
  (List.get! (List.get! result i) j) = 
  (List.get! (List.get! matrix i) j) := sorry

theorem input_preservation :
  ∀ (matrix : List (List Int)),
  let result := reverseOnDiagonals matrix
  matrix = matrix := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval reverse_on_diagonals [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval reverse_on_diagonals [[239]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval reverse_on_diagonals [[1, 10], [100, 1000]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded