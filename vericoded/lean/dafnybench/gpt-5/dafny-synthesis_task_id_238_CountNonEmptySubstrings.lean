import Mathlib
-- <vc-preamble>
import Init
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma cast_length_nonneg (s : String) : 0 ≤ (s.length : Int) := by
  simpa using (Int.ofNat_nonneg s.length)
-- </vc-helpers>

-- <vc-definitions>
def CountNonEmptySubstrings (s : String) : Int :=
((s.length : Int) * ((s.length : Int) + 1)) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem CountNonEmptySubstrings_spec (s : String) :
let count := CountNonEmptySubstrings s
count ≥ 0 ∧ count = (s.length * (s.length + 1)) / 2 :=
by
  intro count
  have hdef : count = CountNonEmptySubstrings s := rfl
  constructor
  ·
    have hlen : 0 ≤ (s.length : Int) := cast_length_nonneg s
    have hsum : 0 ≤ (s.length : Int) + 1 := add_nonneg hlen (by decide)
    have hmul : 0 ≤ (s.length : Int) * ((s.length : Int) + 1) := mul_nonneg hlen hsum
    have hdiv : 0 ≤ ((s.length : Int) * ((s.length : Int) + 1)) / 2 := by
      simpa using (Int.ediv_nonneg hmul (by decide))
    simpa [hdef, CountNonEmptySubstrings] using hdiv
  ·
    simpa [hdef, CountNonEmptySubstrings]
-- </vc-theorems>
