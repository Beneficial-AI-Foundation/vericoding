-- <vc-helpers>
-- </vc-helpers>

def countSubstr (s₁ s₂ : String) : Nat := sorry 

def obfuscate (email : String) : String := 
  sorry

theorem obfuscate_no_at_or_dot (email : String) :
  ¬ (obfuscate email).contains '@' ∧ ¬ (obfuscate email).contains '.' := sorry 

theorem obfuscate_reversible (email : String) :
  ((obfuscate email).replace " [at] " "@").replace " [dot] " "." = email := sorry

theorem obfuscate_empty :
  obfuscate "" = "" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible