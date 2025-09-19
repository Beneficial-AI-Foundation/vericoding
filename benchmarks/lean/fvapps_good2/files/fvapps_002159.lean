-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bitadd (idx : Nat) (val : Int) (bit : Array Int) : Array Int :=
  sorry

def bitsum (idx : Nat) (bit : Array Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bitadd_inverse (idx : Nat) (val : Int) (bit : Array Int) :
  bitsum idx (bitadd idx (-val) (bitadd idx val bit)) = bitsum idx bit :=
sorry

theorem bitadd_retrieval (idx : Nat) (val : Int) (bit : Array Int) :
  bitsum idx (bitadd idx val bit) = bitsum idx bit + val :=
sorry
-- </vc-theorems>