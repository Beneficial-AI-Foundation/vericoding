def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result: Int) :=
(result ∣ a) ∧
(result ∣ b) ∧
(∀ (d': Int),
(d' > 0) → (d' ∣ a) → (d' ∣ b) →
d' ≤ result);
-- program termination
∃ result, implementation a b = result ∧
spec result

-- LLM HELPER
def gcd (a b: Int) : Int :=
if b = 0 then Int.natAbs a
else gcd b (a % b)

def implementation (a b: Int) : Int := gcd a b

-- LLM HELPER
lemma gcd_dvd_left (a b: Int) : gcd a b ∣ a := by
  sorry

-- LLM HELPER
lemma gcd_dvd_right (a b: Int) : gcd a b ∣ b := by
  sorry

-- LLM HELPER
lemma gcd_greatest (a b d: Int) : d > 0 → d ∣ a → d ∣ b → d ≤ gcd a b := by
  sorry

theorem correctness
(a b: Int)
: problem_spec implementation a b := by
  use gcd a b
  constructor
  · rfl
  · constructor
    · exact gcd_dvd_left a b
    · constructor
      · exact gcd_dvd_right a b
      · exact gcd_greatest a b