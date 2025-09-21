-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zeros (n : Nat) : Vector Int n :=
sorry

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i.val] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 :=
sorry
-- </vc-theorems>