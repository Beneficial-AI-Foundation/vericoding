-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfABeach (s : String) : Nat :=
  sorry

def substringExists (s : String) (substr : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_beach_words (s : String) :
  (¬ substringExists s "sand" ∧ ¬ substringExists s "SAND") →
  (¬ substringExists s "water" ∧ ¬ substringExists s "WATER") →
  (¬ substringExists s "fish" ∧ ¬ substringExists s "FISH") →
  (¬ substringExists s "sun" ∧ ¬ substringExists s "SUN") →
  sumOfABeach s = 0 :=
sorry

theorem output_range (s : String) :
  sumOfABeach s ≥ 0 ∧ sumOfABeach s ≤ s.length :=
sorry
-- </vc-theorems>