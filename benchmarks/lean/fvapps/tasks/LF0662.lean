-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_different_arrays (N: Nat) (M: Nat) (K: Nat) (A: List Nat) : Nat :=
  sorry

@[simp] theorem count_different_arrays_in_range
  (N M K: Nat) (A: List Nat)
  (h1: N ≥ 1) (h2: M ≥ 1) (h3: K ≥ 1)  
  (h4: A.length = N)
  (h5: ∀ x ∈ A, x ≥ 1 ∧ x ≤ M) :
  1 ≤ count_different_arrays N M K A ∧ 
  count_different_arrays N M K A ≤ 10^9 + 7 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_different_arrays_single_element
  (M K: Nat) (A: List Nat)
  (h1: M ≥ 1) (h2: K ≥ 1)
  (h3: A.length = 1)
  (h4: ∀ x ∈ A, x ≥ 1 ∧ x ≤ M) :
  count_different_arrays 1 M K A = 1 :=
sorry

theorem count_different_arrays_symmetry 
  (N M K: Nat) (A: List Nat)
  (h1: N ≥ 1) (h2: M ≥ 1) (h3: K ≥ 1)
  (h4: A.length = N)
  (h5: ∀ x ∈ A, x ≥ 1 ∧ x ≤ M) :
  count_different_arrays N M K A = 
  count_different_arrays N M K A.reverse :=
sorry

theorem count_different_arrays_monotone_K
  (N M K: Nat) (A: List Nat)
  (h1: N ≥ 1) (h2: M ≥ 1) (h3: K > 1)
  (h4: A.length = N)
  (h5: ∀ x ∈ A, x ≥ 1 ∧ x ≤ M) :
  count_different_arrays N M K A ≤ 
  count_different_arrays N M (K-1) A :=
sorry
-- </vc-theorems>