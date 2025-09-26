import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def natToInt (n : Nat) : Int := Int.ofNat n

-- </vc-helpers>

-- <vc-definitions>
def CountLists (lists : Array (Array Int)) : Int :=
Int.ofNat lists.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountLists_spec (lists : Array (Array Int)) :
let count := CountLists lists
count ≥ 0 ∧ count = lists.size :=
by
  dsimp [CountLists]
  constructor
  · apply Int.ofNat_nonneg
  · rfl

-- </vc-theorems>
