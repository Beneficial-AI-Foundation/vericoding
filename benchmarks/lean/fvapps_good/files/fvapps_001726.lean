-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hamming (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_positive (n : Nat) (h : n > 0) :
  hamming n > 0 :=
sorry

theorem hamming_strictly_increasing (n : Nat) (h : n > 1) :
  hamming n > hamming (n-1) :=
sorry

theorem hamming_monotone (n1 n2 : Nat) (h1 : n1 > 0) (h2 : n2 > 0) :
  n1 ≤ n2 → hamming n1 ≤ hamming n2 :=
sorry

theorem hamming_first_values :
  hamming 1 = 1 ∧ hamming 2 = 2 ∧ hamming 3 = 3 :=
sorry
-- </vc-theorems>