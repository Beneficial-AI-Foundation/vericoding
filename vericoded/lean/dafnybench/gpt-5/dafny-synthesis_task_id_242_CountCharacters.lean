import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
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
  have hge : (0 : Int) ≤ Int.ofNat s.length := Int.ofNat_nonneg _
  have heq : Int.ofNat s.length = (s.length : Int) := rfl
  simpa [CountCharacters] using And.intro hge heq
-- </vc-theorems>
