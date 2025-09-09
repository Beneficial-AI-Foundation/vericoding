-- <vc-helpers>
-- </vc-helpers>

def wheres_wally (s : String) : Int := sorry

theorem valid_wally_matches 
  {p s : String}
  (h1 : p.isEmpty ∨ p.endsWith " ")
  (h2 : s = "" ∨ s = "." ∨ s = "," ∨ s = " " ∨ s = "'") : 
  ∃ pos : Int, pos ≥ 0 ∧ 
  pos = wheres_wally (String.append (String.append p "Wally") s) := sorry

theorem invalid_wally_no_match 
  {s : String}
  (h1 : s.all (fun c => c ≠ 'W') ∨ 
        ∃ (c d : Char), c.isAlpha ∧ d.isAlpha) :
  wheres_wally s = -1 := sorry

theorem wally_word_boundaries 
  {p s : String} :
  wheres_wally (String.append (String.append p "Wall") s) = -1 ∧ 
  wheres_wally (String.append (String.append p "Wallys") s) = -1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval wheres_wally "Wally"

/-
info: 3
-/
-- #guard_msgs in
-- #eval wheres_wally "Hi Wally."

/-
info: -1
-/
-- #guard_msgs in
-- #eval wheres_wally "Where"s Waldo"

-- Apps difficulty: introductory
-- Assurance level: unguarded