-- <vc-helpers>
-- </vc-helpers>

def maxUniqueSplit (s: String) : Nat := sorry

theorem maxUniqueSplit_single_char (s: String) (h: s.length = 1) :
  maxUniqueSplit s = 1 := sorry

theorem maxUniqueSplit_aa : 
  maxUniqueSplit "aa" = 1 := sorry

theorem maxUniqueSplit_aba :
  maxUniqueSplit "aba" = 2 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible