-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def change_case (s : String) (target : String) : Option String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mixed_formats_returns_none (s : String) :
  (s.contains '_' && s.contains '-') ∨ 
  (s.contains '_' && s ≠ s.toLower) ∨
  (s.contains '-' && s ≠ s.toLower) →
  change_case s "snake" = none ∧ 
  change_case s "kebab" = none ∧
  change_case s "camel" = none :=
  sorry

theorem invalid_target_returns_none (s target : String) :
  target ≠ "snake" ∧ target ≠ "kebab" ∧ target ≠ "camel" →
  change_case s target = none :=
  sorry

theorem single_word_unchanged (s : String) :
  s.all (fun c => c.isLower) →
  change_case s "snake" = some s ∧
  change_case s "kebab" = some s ∧
  change_case s "camel" = some s :=
  sorry

theorem empty_string (target : String) :
  (target = "snake" ∨ target = "kebab" ∨ target = "camel") →
  change_case "" target = some "" :=
  sorry
-- </vc-theorems>