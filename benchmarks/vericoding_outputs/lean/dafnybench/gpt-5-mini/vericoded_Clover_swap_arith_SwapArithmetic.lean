import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Simple helper: identity on pairs of Int

def idPair (p : Int × Int) : Int × Int := p

-- </vc-helpers>

-- <vc-definitions>
def SwapArithmetic (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapArithmetic_spec (X Y : Int) :
let (x, y) := SwapArithmetic X Y
x = Y ∧ y = X :=
by
  dsimp [SwapArithmetic]
  constructor
  all_goals rfl

-- </vc-theorems>
