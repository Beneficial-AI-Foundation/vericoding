import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no extra helpers needed
-- </vc-helpers>

-- <vc-definitions>
def zeros (n : Nat) : Vector Int n :=
Vector.ofFn (fun _ => (0 : Int))

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows :=
Vector.ofFn (fun _ => zeros cols)
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i.val] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 :=
by
  intro i
  constructor
  ·
    have hi : i.val < n := i.isLt
    change (zeros n).get ⟨i.val, hi⟩ = 0
    simp [zeros]
  ·
    intro rows cols i j
    have hi : i.val < rows := i.isLt
    have hj : j.val < cols := j.isLt
    change ((zeros2d rows cols).get ⟨i.val, hi⟩).get ⟨j.val, hj⟩ = 0
    simp [zeros2d, zeros]
-- </vc-theorems>
