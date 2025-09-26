import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem pair_destruct_eq {α β} (a : α) (b : β) :
  let (x, y) := (a, b)
  x = a ∧ y = b := by
  exact And.intro rfl rfl
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
  simpa [SwapSimultaneous] using (pair_destruct_eq Y X)
-- </vc-theorems>
