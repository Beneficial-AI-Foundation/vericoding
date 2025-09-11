-- <vc-preamble>
def solve (s : String) : String := sorry

def isUpper (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLower (s : String) : Bool := sorry

theorem solve_returns_either_upper_or_lower (s : String) : 
  (solve s = s.toUpper) ∨ (solve s = s.toLower) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_preserves_uppercase (s : String) : 
  isUpper s = true → solve s = s.toUpper := sorry 

theorem solve_preserves_lowercase (s : String) :
  isLower s = true → solve s = s.toLower := sorry

theorem solve_preserves_length (s : String) :
  (solve s).length = s.length := sorry

/-
info: 'code'
-/
-- #guard_msgs in
-- #eval solve "coDe"

/-
info: 'CODE'
-/
-- #guard_msgs in
-- #eval solve "CODe"

/-
info: 'code'
-/
-- #guard_msgs in
-- #eval solve "coDE"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded