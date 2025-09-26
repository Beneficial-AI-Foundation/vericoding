import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem let_pair_uint8 (a b : UInt8) :
    (let (x, y) := (a, b); x = a ∧ y = b) := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def SwapBitvectors (X Y : UInt8) : UInt8 × UInt8 :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapBitvectors_spec (X Y : UInt8) :
let (x, y) := SwapBitvectors X Y
x = Y ∧ y = X :=
by
  dsimp [SwapBitvectors]
  exact ⟨rfl, rfl⟩
-- </vc-theorems>
