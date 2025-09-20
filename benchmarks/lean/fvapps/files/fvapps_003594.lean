-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countSubstr (s₁ s₂ : String) : Nat := sorry 

def obfuscate (email : String) : String := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem obfuscate_no_at_or_dot (email : String) :
  ¬ (obfuscate email).contains '@' ∧ ¬ (obfuscate email).contains '.' := sorry 

theorem obfuscate_reversible (email : String) :
  ((obfuscate email).replace " [at] " "@").replace " [dot] " "." = email := sorry

theorem obfuscate_empty :
  obfuscate "" = "" := sorry
-- </vc-theorems>