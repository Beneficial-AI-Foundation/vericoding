-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Nat) : Nat :=
  sorry

def isValidPos (pos : String) : Bool :=
  sorry

def knight (s e : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem knight_valid_range {s e : String}
  (h1 : isValidPos s) (h2 : isValidPos e) :
  let m := knight s e
  0 ≤ m ∧ m ≤ 6 :=
sorry

theorem knight_same_position {p : String}
  (h : isValidPos p) :
  knight p p = 0 :=
sorry

theorem knight_diagonal_adjacent {s e : String}
  (h1 : isValidPos s) (h2 : isValidPos e)
  (h3 : abs ((s.get! ⟨0⟩).toNat - (e.get! ⟨0⟩).toNat) = 1)
  (h4 : abs ((s.get! ⟨1⟩).toNat - (e.get! ⟨1⟩).toNat) = 1) :
  knight s e = 2 :=
sorry

theorem knight_symmetric {p t : String}
  (h1 : isValidPos p) (h2 : isValidPos t) :
  knight p t = knight t p :=
sorry
-- </vc-theorems>