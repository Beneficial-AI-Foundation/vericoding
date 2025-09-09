def firstIndex (s: String) (c: Char) : Nat :=
  sorry

def lastIndex (s: String) (c: Char) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def solve (s: String) : Char :=
  sorry

theorem solve_returns_char_from_input (s: String) (h: s.length > 0) :
  ∃ p: String.Pos, solve s = s.get p :=
  sorry

theorem solve_returns_char_with_minimal_first_last_diff (s: String) (h: s.length > 0) :
  ∀ c: Char, 
  firstIndex s (solve s) - lastIndex s (solve s) 
  ≤ firstIndex s c - lastIndex s c :=
  sorry

theorem solve_returns_lexicographically_first_when_tied (s: String) (h: s.length > 0) :
  ∀ c: Char,
  (firstIndex s c - lastIndex s c = firstIndex s (solve s) - lastIndex s (solve s))
  → solve s ≤ c :=
  sorry

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval solve "a"

/-
info: 'x'
-/
-- #guard_msgs in
-- #eval solve "axyzxyz"

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval solve "dcbadcba"

-- Apps difficulty: introductory
-- Assurance level: unguarded