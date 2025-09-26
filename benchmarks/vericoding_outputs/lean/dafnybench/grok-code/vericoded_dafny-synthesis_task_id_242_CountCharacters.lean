import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  have h : (Int.ofNat s.length) ≥ 0 := Int.ofNat_nonneg s.length
  exact And.intro h rfl
-- </vc-theorems>
