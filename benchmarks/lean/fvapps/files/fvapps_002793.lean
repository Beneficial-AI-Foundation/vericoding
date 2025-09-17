-- <vc-preamble>
def solve (s : String) : Int := sorry

def isVowel (c : Char) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isConsonant (c : Char) : Bool := sorry

theorem solve_returns_nonnegative (s : String) : 
  solve s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 26
-/
-- #guard_msgs in
-- #eval solve "zodiac"

/-
info: 57
-/
-- #guard_msgs in
-- #eval solve "strength"

/-
info: 73
-/
-- #guard_msgs in
-- #eval solve "catchphrase"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible