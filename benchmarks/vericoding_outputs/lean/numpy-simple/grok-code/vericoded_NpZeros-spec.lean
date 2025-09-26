import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def zeros (n : Nat) : Vector Int n :=
Vector.replicate n (0 : Int)

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows :=
Vector.replicate rows (Vector.replicate cols (0 : Int))
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i.val] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 :=
by
  intro i
  constructor
  · simp [zeros]
  · intros rows cols i' j'
    simp [zeros2d]
-- </vc-theorems>
