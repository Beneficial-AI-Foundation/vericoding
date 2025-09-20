-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def wheres_wally (s : String) : Int := sorry

theorem valid_wally_matches 
  {p s : String}
  (h1 : p.isEmpty ∨ p.endsWith " ")
  (h2 : s = "" ∨ s = "." ∨ s = "," ∨ s = " " ∨ s = "'") : 
  ∃ pos : Int, pos ≥ 0 ∧ 
  pos = wheres_wally (String.append (String.append p "Wally") s) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_wally_no_match 
  {s : String}
  (h1 : s.all (fun c => c ≠ 'W') ∨ 
        ∃ (c d : Char), c.isAlpha ∧ d.isAlpha) :
  wheres_wally s = -1 := sorry

theorem wally_word_boundaries 
  {p s : String} :
  wheres_wally (String.append (String.append p "Wall") s) = -1 ∧ 
  wheres_wally (String.append (String.append p "Wallys") s) = -1 := sorry
-- </vc-theorems>