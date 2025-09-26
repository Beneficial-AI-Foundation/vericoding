import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- LLM HELPER - convert a Nat to an Int (alias) -/
def natToInt (n : Nat) : Int := Int.ofNat n

/-- LLM HELPER - natToInt is nonnegative -/
theorem natToInt_nonneg (n : Nat) : natToInt n ≥ 0 := by
  dsimp [natToInt]
  exact Int.ofNat_nonneg n
-- </vc-helpers>

-- <vc-definitions>
def CountCharacters (s : String) : Int :=
natToInt s.length
-- </vc-definitions>

-- <vc-theorems>
theorem CountCharacters_spec (s : String) :
let count := CountCharacters s
count ≥ 0 ∧ count = s.length :=
by
  dsimp [CountCharacters]
  constructor
  · exact natToInt_nonneg s.length
  · rfl
-- </vc-theorems>
