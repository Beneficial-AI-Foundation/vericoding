-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidTree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
sorry

def maxHappiness (n k : Nat) (edges : List (Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxHappiness_valid_tree (n : Nat) (k : Nat)
  (edges : List (Nat × Nat)) :
  isValidTree n edges → True :=
sorry

theorem maxHappiness_nonnegative (n : Nat) (k : Nat)
  (edges : List (Nat × Nat)) :
  isValidTree n edges → maxHappiness n k edges ≥ 0 :=
sorry

theorem maxHappiness_zero_when_k_geq_n (n : Nat) (k : Nat)
  (edges : List (Nat × Nat)) :
  isValidTree n edges →
  k ≥ n →
  maxHappiness n k edges = 0 :=
sorry
-- </vc-theorems>