-- <vc-preamble>
def List.unique {α} [BEq α] : List α → List α 
  | [] => []
  | h::t => if t.contains h then unique t else h :: unique t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def subarraysWithKDistinct (A : List Nat) (K : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem k_validity {A : List Nat} {K : Nat}
  (hA : A.length > 0)
  (hAelems : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 100)
  (hK : 1 ≤ K ∧ K ≤ 50)
  (hKvalid : K ≤ (A.unique).length) :
  0 ≤ subarraysWithKDistinct A K :=
  sorry

theorem k_one {A : List Nat}
  (hA : A.length > 0) 
  (hAelems : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 10) :
  subarraysWithKDistinct A 1 ≥ A.length :=
  sorry

theorem k_equals_distinct {A : List Nat}
  (hA : A.length > 0)
  (hAelems : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 100) :
  subarraysWithKDistinct A (A.unique).length ≥ 1 :=
  sorry

theorem edge_cases :
  subarraysWithKDistinct [1] 1 = 1 ∧ 
  subarraysWithKDistinct [1, 1] 1 = 3 ∧
  subarraysWithKDistinct [1, 2, 3] 3 = 1 :=
  sorry
-- </vc-theorems>