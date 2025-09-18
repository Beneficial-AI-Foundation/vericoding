-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hammingDistance (x y : Nat) : Nat :=
  sorry

def bitLength (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_distance_symmetry (x y : Nat) :
  hammingDistance x y = hammingDistance y x :=
sorry

theorem hamming_distance_self (x : Nat) :
  hammingDistance x x = 0 :=
sorry

theorem hamming_distance_nonnegative (x y : Nat) :
  hammingDistance x y ≥ 0 :=
sorry

theorem hamming_distance_upper_bound (x y : Nat) :
  hammingDistance x y ≤ max (bitLength x) (bitLength y) :=
sorry
-- </vc-theorems>