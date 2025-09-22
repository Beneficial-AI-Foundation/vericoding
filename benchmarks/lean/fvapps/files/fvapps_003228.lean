-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Nat.toBin (n : Nat) : String := sorry

def grille (message : String) (code : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grille_length_leq_input (message : String) (code : Nat) :
  (grille message code).length ≤ message.length := sorry

theorem grille_chars_subset_input (message : String) (code : Nat) :
  ∀ c, c ∈ (grille message code).data → c ∈ message.data := sorry

theorem grille_length_leq_ones (message : String) (code : Nat) :
  (grille message code).length ≤ (code.toBin.data.filter (· = '1')).length := sorry

theorem grille_empty_input (code : Nat) :
  grille "" code = "" := sorry

theorem grille_zero_code (message : String) :
  grille message 0 = "" := sorry
-- </vc-theorems>