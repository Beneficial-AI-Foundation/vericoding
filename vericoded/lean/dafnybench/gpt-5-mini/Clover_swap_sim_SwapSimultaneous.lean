import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCHelpers
-- LLM HELPER
/-- identity helper for Int used in proofs/examples -/
def idInt (n : Int) : Int := n
end VCHelpers
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
  dsimp [SwapSimultaneous]
  constructor
  all_goals rfl
-- </vc-theorems>
