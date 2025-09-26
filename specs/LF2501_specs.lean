-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_probability_of_a (letters: List Letter) (k: Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prob_between_zero_and_one (letters: List Letter) (k: Nat) (h: k ≤ letters.length) :
  let prob := calc_probability_of_a letters k
  0 ≤ prob ∧ prob ≤ 1 := by
  sorry

theorem no_a_prob_zero (letters: List Letter) (k: Nat) (h1: k ≤ letters.length)
  (h2: ¬ (letters.contains Letter.a)) :
  calc_probability_of_a letters k = 0 := by
  sorry

theorem all_letters_k_prob_one (letters: List Letter) (k: Nat)
  (h1: k = letters.length) (h2: letters.contains Letter.a) : 
  calc_probability_of_a letters k = 1 := by
  sorry

theorem all_a_prob_one (letters: List Letter) (k: Nat) 
  (h1: k ≤ letters.length) (h2: ∀ l ∈ letters, l = Letter.a) :
  calc_probability_of_a letters k = 1 := by
  sorry

theorem only_a_letters_prob_one (letters: List Letter) (k: Nat)
  (h1: k ≤ letters.length) (h2: ∀ l ∈ letters, l = Letter.a) :
  calc_probability_of_a letters k = 1 := by
  sorry

theorem no_a_letters_prob_zero (letters: List Letter) (k: Nat)
  (h1: k ≤ letters.length) (h2: ∀ l ∈ letters, l ≠ Letter.a) :
  calc_probability_of_a letters k = 0 := by
  sorry
-- </vc-theorems>