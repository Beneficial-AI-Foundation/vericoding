-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_lock_ness_monster : String → Bool := sorry

theorem is_lock_ness_monster_case_insensitive (s : String) :
  is_lock_ness_monster s = is_lock_ness_monster (s.toUpper) ∧
  is_lock_ness_monster s = is_lock_ness_monster (s.toLower) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_lock_ness_monster_contains_phrase (s : String) (phrase : String) 
  (h : phrase = "tree fiddy" ∨ phrase = "three fifty" ∨ phrase = "3.50") :
  is_lock_ness_monster (s ++ phrase ++ s) = true :=
sorry

theorem is_lock_ness_monster_no_substring (s : String) 
  (h : s.length > 0) :
  (¬is_lock_ness_monster s) ↔ 
  (¬(s.data.asString.contains '3') ∧ 
   ¬(s.data.asString.contains 't') ∧
   ¬(s.data.asString.contains 'f')) :=
sorry

theorem is_lock_ness_monster_empty :
  is_lock_ness_monster "" = false :=
sorry

theorem is_lock_ness_monster_whitespace (s : String)
  (h : s = " " ∨ s = "\n" ∨ s = "\t") :
  is_lock_ness_monster s = false :=
sorry
-- </vc-theorems>