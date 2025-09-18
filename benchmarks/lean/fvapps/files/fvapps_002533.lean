-- <vc-preamble>
def solve (s : String) : Bool := sorry

def stringReverse (s : String) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getMismatches (s : String) : Nat := sorry

theorem solve_distance_property (s : String) 
    (h : s.length > 0) 
    (h2 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b' ∨ c = 'c') :
  let mismatches := getMismatches s
  solve s = (mismatches = 1 ∨ (mismatches = 0 ∧ s.length % 2 = 1)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_symmetry_property (s : String) (h : s.length > 0) :
  solve s = solve (stringReverse s) := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval solve "abba"

/-
info: True
-/
-- #guard_msgs in
-- #eval solve "abbaa"

/-
info: True
-/
-- #guard_msgs in
-- #eval solve "abbx"

/-
info: False
-/
-- #guard_msgs in
-- #eval solve "aa"

/-
info: True
-/
-- #guard_msgs in
-- #eval solve "ab"

/-
info: True
-/
-- #guard_msgs in
-- #eval solve "abcba"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded