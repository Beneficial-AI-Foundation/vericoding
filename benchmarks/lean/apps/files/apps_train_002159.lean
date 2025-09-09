def bitadd (idx : Nat) (val : Int) (bit : Array Int) : Array Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def bitsum (idx : Nat) (bit : Array Int) : Int :=
  sorry

theorem bitadd_inverse (idx : Nat) (val : Int) (bit : Array Int) : 
  bitsum idx (bitadd idx (-val) (bitadd idx val bit)) = bitsum idx bit :=
  sorry

theorem bitadd_retrieval (idx : Nat) (val : Int) (bit : Array Int) :
  bitsum idx (bitadd idx val bit) = bitsum idx bit + val :=
  sorry

-- Apps difficulty: competition
-- Assurance level: unguarded