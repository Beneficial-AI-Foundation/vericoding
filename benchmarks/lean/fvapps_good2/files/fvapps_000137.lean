-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minDeletionSize (A : List (List Char)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (A : List (List Char)) (h : A.all (λ s => s.length = A.head!.length)) :
  let result := minDeletionSize A
  0 ≤ result ∧ result ≤ A.head!.length :=
sorry

theorem sorted_columns_zero_deletions (A : List (List Char)) (h : A.all (λ s => s.length = A.head!.length)) :
  let sorted_columns := A
  minDeletionSize sorted_columns = 0 :=
sorry

theorem reverse_sorted_most_deletions (A : List (List Char)) (h₁ : A ≠ []) (h₂ : A.all (λ s => s.length = A.head!.length)) :
  let reverse_sorted := A
  minDeletionSize reverse_sorted ≤ A.head!.length :=
sorry

theorem identical_strings_zero_deletions (A : List (List Char)) (s : List Char)
    (h₁ : A ≠ []) (h₂ : A.all (λ str => str = s)) :
  minDeletionSize A = 0 :=
sorry
-- </vc-theorems>