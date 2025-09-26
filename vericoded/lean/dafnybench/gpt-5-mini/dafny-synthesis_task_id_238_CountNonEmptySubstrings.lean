import Mathlib
-- <vc-preamble>
import Init
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem Int_natCast_nonneg (n : Nat) : 0 ≤ (n : Int) := by
  exact Int.natCast_nonneg n

-- </vc-helpers>

-- <vc-definitions>
def CountNonEmptySubstrings (s : String) : Int :=
(s.length * (s.length + 1) / 2 : Int)
-- </vc-definitions>

-- <vc-theorems>
theorem CountNonEmptySubstrings_spec (s : String) :
let count := CountNonEmptySubstrings s
count ≥ 0 ∧ count = (s.length * (s.length + 1)) / 2 :=
by
  dsimp [CountNonEmptySubstrings]
  let n := s.length
  have h_nonneg : 0 ≤ ((n * (n + 1) / 2) : Int) := Int.natCast_nonneg (n * (n + 1) / 2)
  constructor
  · exact h_nonneg
  · rfl

-- </vc-theorems>
