-- <vc-helpers>
-- </vc-helpers>

def case_unification (s : String) : String := sorry

theorem case_unification_preserves_length (s : String) 
  (h : s.length > 0) : 
  (case_unification s).length = s.length := sorry

theorem already_upper_stays_upper (s : String)
  (h1 : s.length > 0)
  (h2 : ∀ c ∈ s.data, c.isUpper) :
  case_unification s = s.toUpper := sorry 

theorem already_lower_stays_lower (s : String)
  (h1 : s.length > 0) 
  (h2 : ∀ c ∈ s.data, c.isLower) :
  case_unification s = s.toLower := sorry

/-
info: 'aba'
-/
-- #guard_msgs in
-- #eval case_unification "Aba"

/-
info: 'ABA'
-/
-- #guard_msgs in
-- #eval case_unification "ABa"

/-
info: 'asdervt'
-/
-- #guard_msgs in
-- #eval case_unification "asdERvT"

-- Apps difficulty: introductory
-- Assurance level: unguarded