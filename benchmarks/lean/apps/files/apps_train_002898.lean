-- <vc-helpers>
-- </vc-helpers>

def lcs (x y : String) : String := sorry

def isSubsequence (s t : String) : Bool := sorry

theorem lcs_empty_string 
  (x y : String) :
  lcs "" y = "" ∧ lcs x "" = "" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible