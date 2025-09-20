-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countChars (s : String) (c : Char) : Nat :=
  sorry

def remove_exclamation_marks (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_exclamation_in_result (s : String) :
  ¬(remove_exclamation_marks s).contains '!' := by
sorry

theorem length_after_removal (s : String) :
  (remove_exclamation_marks s).length = s.length - (countChars s '!') := by
sorry

theorem result_equals_remove_exclamation (s : String) :
  (remove_exclamation_marks s).replace "!" "" = remove_exclamation_marks s := by
sorry

theorem unchanged_without_exclamation (s : String) (h : ¬s.contains '!') :
  remove_exclamation_marks s = s := by
sorry

theorem concatenation_property (s₁ s₂ : String) :
  remove_exclamation_marks s₁ ++ remove_exclamation_marks s₂ =
  remove_exclamation_marks (s₁ ++ s₂) := by
sorry
-- </vc-theorems>