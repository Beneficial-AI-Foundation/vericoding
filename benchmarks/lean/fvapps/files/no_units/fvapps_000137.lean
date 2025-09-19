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
-- </vc-theorems>