-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def move_ten (s : String) : String := sorry

def isLower (c : Char) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem move_ten_preserves_length (s : String) : 
  (move_ten s).length = s.length := sorry

theorem move_ten_keeps_lowercase (s : String) :
  ∀ c, c ∈ (move_ten s).data → isLower c := sorry 

theorem move_ten_reversible (s : String) :
  ∃ f : String → String, f (move_ten s) = s := sorry

theorem move_ten_idempotent (s : String) :
  move_ten (move_ten s) = move_ten s := sorry

theorem move_ten_homomorphic (s₁ s₂ : String) :
  move_ten (s₁ ++ s₂) = move_ten s₁ ++ move_ten s₂ := sorry
-- </vc-theorems>