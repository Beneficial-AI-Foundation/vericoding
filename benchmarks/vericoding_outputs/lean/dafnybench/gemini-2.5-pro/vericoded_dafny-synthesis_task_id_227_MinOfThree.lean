import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def MinOfThree (a b c : Int) : Int :=
min a (min b c)
-- </vc-definitions>

-- <vc-theorems>
theorem MinOfThree_spec (a b c : Int) :
let min := MinOfThree a b c
min ≤ a ∧ min ≤ b ∧ min ≤ c ∧ (min = a ∨ min = b ∨ min = c) :=
by
  dsimp [MinOfThree]
  constructor
  · exact min_le_left a (min b c)
  · constructor
    · exact (min_le_right a (min b c)).trans (min_le_left b c)
    · constructor
      · exact (min_le_right a (min b c)).trans (min_le_right b c)
      · rcases min_choice a (min b c) with h | hmbc
        · exact Or.inl h
        · rcases min_choice b c with h' | h''
          · rw [hmbc, h']
            exact Or.inr (Or.inl rfl)
          · rw [hmbc, h'']
            exact Or.inr (Or.inr rfl)
-- </vc-theorems>
