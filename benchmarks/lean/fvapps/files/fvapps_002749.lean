-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem words_preserved (s : String) :
  ∀ w, w ∈ (s.split (· = ' ')) →
  (¬ ('!' ∈ w.data)) →
  w ∈ (remove s).split (· = ' ') :=
sorry

theorem no_trailing_exclamations (s : String) :
  ∀ w, w ∈ (remove s).split (· = ' ') →
  ¬ w.endsWith "!" :=
sorry

theorem leading_exclamations_preserved (s : String) :
  ∀ w w', w ∈ s.split (· = ' ') →
  w' ∈ (remove s).split (· = ' ') →
  w.startsWith "!" → w' = w ∨ w'.startsWith "!" :=
sorry
-- </vc-theorems>