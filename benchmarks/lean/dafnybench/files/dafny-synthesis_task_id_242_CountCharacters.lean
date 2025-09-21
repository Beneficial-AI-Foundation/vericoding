-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountCharacters (s : String) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountCharacters_spec (s : String) :
let count := CountCharacters s
count ≥ 0 ∧ count = s.length :=
sorry
-- </vc-theorems>