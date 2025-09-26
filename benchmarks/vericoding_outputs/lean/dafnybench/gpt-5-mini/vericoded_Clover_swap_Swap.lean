import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER

theorem pair_proj_eq {α β : Type} (a : α) (b : β) : Prod.fst (b, a) = b ∧ Prod.snd (b, a) = a := by
  simp

-- </vc-helpers>

-- <vc-definitions>
def Swap (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem Swap_spec (X Y : Int) :
let (x, y) := Swap X Y
x = Y ∧ y = X :=
by
  dsimp [Swap]
  constructor
  rfl
  rfl

-- </vc-theorems>
