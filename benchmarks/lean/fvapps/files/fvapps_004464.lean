-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def x (n : Nat) : List (List Nat) := sorry

theorem square_matrix (n : Nat) (h: n > 0) :
  let result := x n
  List.length result = n ∧
  ∀ row ∈ result, List.length row = n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_ones (n : Nat) (h: n > 0) :
  let result := x n
  (∀ i, i < n → List.get! (List.get! result i) i = 1) ∧
  (∀ i, i < n → List.get! (List.get! result i) (n-1-i) = 1) :=
sorry

theorem non_diagonal_zeros (n : Nat) (h: n > 0) :
  let result := x n
  ∀ i j, i < n → j < n → i ≠ j → j ≠ (n-1-i) →
    List.get! (List.get! result i) j = 0 :=
sorry

theorem symmetry (n : Nat) (h: n > 0) :
  let result := x n
  (∀ i j, i < n → j < n → List.get! (List.get! result i) j = 
              List.get! (List.get! result (n-1-i)) (n-1-j)) ∧
  (∀ i j, i < n → j < n → List.get! (List.get! result i) j = 
              List.get! (List.get! result j) i) :=
sorry
-- </vc-theorems>