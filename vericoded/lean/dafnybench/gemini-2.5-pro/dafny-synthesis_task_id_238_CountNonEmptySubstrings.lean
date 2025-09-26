import Mathlib
-- <vc-preamble>
import Init
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CountNonEmptySubstrings (s : String) : Int :=
  (s.length * (s.length + 1)) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem CountNonEmptySubstrings_spec (s : String) :
let count := CountNonEmptySubstrings s
count ≥ 0 ∧ count = (s.length * (s.length + 1)) / 2 :=
by
  unfold CountNonEmptySubstrings
  dsimp
  constructor
  · apply Int.ofNat_nonneg
  · rfl
-- </vc-theorems>
