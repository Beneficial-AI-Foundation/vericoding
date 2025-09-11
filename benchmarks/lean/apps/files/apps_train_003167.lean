-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def autocorrect (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basic_replacement (s : String)
  (h : s = "u" ∨ (∃ n : Nat, s = "y" ++ String.mk (List.replicate n 'o') ++ "u")) :
  autocorrect s = "your sister" := 
  sorry

theorem no_replacement (s : String)
  (h : ∀ c ∈ s.data, c ≠ 'u' ∧ c ≠ 'y' ∧ c.isAlpha) :
  autocorrect s = s :=
  sorry

theorem multiple_replacements (ls : List String)
  (h : ls ≠ [] ∧ ∀ s ∈ ls, s = "u" ∨ (∃ n : Nat, s = "y" ++ String.mk (List.replicate n 'o') ++ "u")) :
  autocorrect (String.intercalate " " ls) = 
    "your sister" ++ String.mk (List.replicate (ls.length - 1) ' ') ++ 
    String.intercalate " " (List.replicate (ls.length - 1) "your sister") :=
  sorry

/-
info: 'I miss your sister!'
-/
-- #guard_msgs in
-- #eval autocorrect "I miss you!"

/-
info: 'your sister want to go to the movies?'
-/
-- #guard_msgs in
-- #eval autocorrect "u want to go to the movies?"

/-
info: 'I want to film the bayou with your sister and put it on youtube'
-/
-- #guard_msgs in
-- #eval autocorrect "I want to film the bayou with you and put it on youtube"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded