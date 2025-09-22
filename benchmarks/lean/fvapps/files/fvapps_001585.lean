-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def almost_everywhere_zero (n : Nat) (k : Nat) : Nat :=
  sorry

def comb (n : Nat) (k : Nat) : Nat :=
  sorry

def num_digits (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem aez_valid_inputs (n : Nat) (k : Nat) :
  let result := almost_everywhere_zero n k
  result ≥ 0 :=
sorry

theorem aez_zero_k (n : Nat) (h : n > 0) :
  almost_everywhere_zero n 0 = 1 :=
sorry

theorem aez_k_greater_than_digits (n : Nat) (k : Nat) (h1 : n > 0) (h2 : k > num_digits n) :
  almost_everywhere_zero n k = 0 :=
sorry

theorem comb_properties (n k : Nat) :
  let result := comb n k
  (k > n → result = 0) ∧
  ((k = 0 ∨ k = n) → result ≤ 1) ∧
  (k ≤ n → comb n k = comb n (n-k)) :=
sorry

theorem aez_single_nonzero (n : Nat) (h : n > 0) :
  almost_everywhere_zero n 1 ≥ num_digits n :=
sorry
-- </vc-theorems>