-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiply (n k: Nat) : Nat :=
sorry

def isPrime (n: Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_positive (n k: Nat)
  (h1: n > 0) (h2: k > 0) : multiply n k > 0 :=
sorry

theorem multiply_one (k: Nat)
  (h: k > 0) : multiply 1 k = 1 :=
sorry

theorem multiply_k1_is_one (n: Nat)
  (h: n > 0) : multiply n 1 = 1 :=
sorry

theorem multiply_monotone_k (n k: Nat)
  (h1: n > 0) (h2: k > 1) :
  multiply n k ≥ multiply n (k-1) :=
sorry
-- </vc-theorems>