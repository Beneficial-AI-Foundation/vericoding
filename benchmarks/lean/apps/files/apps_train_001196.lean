-- <vc-helpers>
-- </vc-helpers>

def generate_pattern (k : Nat) : List String := sorry

theorem valid_chars {k : Nat} :
  ∀ line ∈ generate_pattern k,
  ∀ c ∈ line.data,
  c.isDigit ∨ c = ' ' := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible