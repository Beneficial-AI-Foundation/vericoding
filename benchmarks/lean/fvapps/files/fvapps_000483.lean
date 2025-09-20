-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestDecomposition (s : String) : Nat :=
  sorry

def isReversed (s : String) : Bool :=
  sorry

def allCharsSame (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decomposition_length {s : String} (h : s ≠ "") :
  1 ≤ longestDecomposition s ∧ longestDecomposition s ≤ s.length :=
sorry

theorem concatenated_decomposition {s : String} (h : s ≠ "") :
  longestDecomposition (s ++ s) ≥ 2 * longestDecomposition s :=
sorry
-- </vc-theorems>