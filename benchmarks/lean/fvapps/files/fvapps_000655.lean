-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinaryString := String 

def compare_signatures (n m : Nat) (sig1 sig2 : List BinaryString) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compare_signatures_non_negative (n m : Nat) (sig1 sig2 : List BinaryString) :
  compare_signatures n m sig1 sig2 ≥ 0 :=
sorry

theorem compare_signatures_upper_bound (n m : Nat) (sig1 sig2 : List BinaryString) :
  compare_signatures n m sig1 sig2 ≤ n * m :=
sorry

theorem compare_signatures_identical (n m : Nat) (sig : List BinaryString) :
  compare_signatures n m sig sig = 0 :=
sorry

theorem compare_signatures_empty (n m : Nat) :
  let emptySignature := List.replicate n ("0")
  compare_signatures n m emptySignature emptySignature = 0 :=
sorry
-- </vc-theorems>