import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helper definitions needed for this simple case
-- </vc-helpers>

-- <vc-definitions>
def CountCharacters (s : String) : Int :=
Int.ofNat s.length
-- </vc-definitions>

-- <vc-theorems>
theorem CountCharacters_spec (s : String) :
let count := CountCharacters s
count ≥ 0 ∧ count = s.length :=
by
  simp only [CountCharacters]
  constructor
  · apply Int.ofNat_nonneg
  · rfl
-- </vc-theorems>
