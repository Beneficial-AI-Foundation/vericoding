-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minDeletionSize (A : List (List Char)) : Nat :=
  sorry

/- Output is bounded between 0 and string length -/
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (A : List (List Char)) (h : A.all (λ s => s.length = A.head!.length)) :
  let result := minDeletionSize A
  0 ≤ result ∧ result ≤ A.head!.length :=
  sorry

/- Already sorted columns need 0 deletions -/

theorem sorted_columns_zero_deletions (A : List (List Char)) (h : A.all (λ s => s.length = A.head!.length)) :
  let sorted_columns := A -- imagine this is the input with sorted columns
  minDeletionSize sorted_columns = 0 :=
  sorry

/- Reverse sorted columns need at most string length deletions -/

theorem reverse_sorted_most_deletions (A : List (List Char)) (h₁ : A ≠ []) (h₂ : A.all (λ s => s.length = A.head!.length)) :
  let reverse_sorted := A -- imagine this is input with reverse sorted columns  
  minDeletionSize reverse_sorted ≤ A.head!.length :=
  sorry

/- Identical strings need 0 deletions -/

theorem identical_strings_zero_deletions (A : List (List Char)) (s : List Char) 
    (h₁ : A ≠ []) (h₂ : A.all (λ str => str = s)) :
  minDeletionSize A = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_deletion_size ["ca", "bb", "ac"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_deletion_size ["xc", "yb", "za"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_deletion_size ["zyx", "wvu", "tsr"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded