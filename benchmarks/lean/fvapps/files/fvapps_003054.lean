-- <vc-preamble>
def sumOfABeach (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def substringExists (s : String) (substr : String) : Bool :=
  sorry

-- Theorem: If a string has no beach words, sum is 0
-- </vc-definitions>

-- <vc-theorems>
theorem no_beach_words (s : String) :
  (¬ substringExists s "sand" ∧ ¬ substringExists s "SAND") →
  (¬ substringExists s "water" ∧ ¬ substringExists s "WATER") →
  (¬ substringExists s "fish" ∧ ¬ substringExists s "FISH") → 
  (¬ substringExists s "sun" ∧ ¬ substringExists s "SUN") →
  sumOfABeach s = 0 :=
sorry

-- Theorem: Output is always non-negative and bounded by string length

theorem output_range (s : String) :
  sumOfABeach s ≥ 0 ∧ sumOfABeach s ≤ s.length :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_of_a_beach "WAtErSlIde"

/-
info: 3
-/
-- #guard_msgs in
-- #eval sum_of_a_beach "GolDeNSanDyWateRyBeaChSuNN"

/-
info: 4
-/
-- #guard_msgs in
-- #eval sum_of_a_beach "gOfIshsunesunFiSh"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded