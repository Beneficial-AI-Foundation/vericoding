-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_preserves_length (s : String) :
  s.length = (remove s).length :=
sorry

theorem remove_preserves_exclamation_count (s : String) :
  (s.data.filter (· = '!')).length = ((remove s).data.filter (· = '!')).length :=
sorry

theorem remove_exclamations_at_end (s : String) : 
  let result := remove s
  let firstExcl := result.data.findIdx (· = '!')
  firstExcl ≠ result.length →
  (∀ i, firstExcl ≤ i ∧ i < result.length → result.data[i]! = '!') ∧
  (∀ i, 0 ≤ i ∧ i < firstExcl → result.data[i]! ≠ '!') :=
sorry

theorem remove_preserves_non_exclamations (s : String) :
  (s.data.filter (· ≠ '!')) = ((remove s).data.filter (· ≠ '!')) := 
sorry
-- </vc-theorems>