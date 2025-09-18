-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove (s : String) : String :=
  sorry

/- If a word in the input string doesn't contain exclamation marks,
    it remains unchanged in the output -/
-- </vc-definitions>

-- <vc-theorems>
theorem words_preserved (s : String) :
  ∀ w, w ∈ (s.split (· = ' ')) → 
  (¬ ('!' ∈ w.data)) → 
  w ∈ (remove s).split (· = ' ') :=
sorry
-- </vc-theorems>