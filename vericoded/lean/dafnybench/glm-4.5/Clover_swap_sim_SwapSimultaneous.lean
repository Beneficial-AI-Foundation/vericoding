import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
lemma pair_eq_iff {α β : Type} (a b : α × β) :
  a = b ↔ a.1 = b.1 ∧ a.2 = b.2 :=
by
  cases a; cases b; simp

lemma eq_symm {α : Type} (a b : α) :
  a = b → b = a :=
by
  intro h
  rw [h]
-- </vc-helpers>

-- <vc-definitions>
def SwapSimultaneous (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapSimultaneous_spec (X Y : Int) :
let (x, y) := SwapSimultaneous X Y
x = Y ∧ y = X :=
by
  unfold SwapSimultaneous
  simp
-- </vc-theorems>
