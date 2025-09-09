-- <vc-helpers>
-- </vc-helpers>

def randomCase (s : String) : String := sorry

theorem randomCase_length_preserved (s : String) : 
  (randomCase s).length = s.length := sorry

theorem randomCase_chars_preserved (s : String) :
  (randomCase s).toLower = s.toLower := sorry

theorem randomCase_changes_some_chars (s : String) 
  (h : s.length ≥ 10) :
  ∃ result, randomCase result ≠ s := sorry

theorem randomCase_only_changes_case (s : String) (i : String.Pos) :
  (s.get i).toLower = ((randomCase s).get i).toLower := sorry

-- Apps difficulty: introductory
-- Assurance level: unguarded