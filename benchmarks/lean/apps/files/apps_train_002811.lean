-- <vc-helpers>
-- </vc-helpers>

def numericals (s : String) : String := sorry

theorem numericals_length_matches_input (s : String) :
  String.length (numericals s) = String.length s := sorry

theorem numericals_only_contains_digits (s : String) :
  ∀ p : String.Pos, ((numericals s).get p).isDigit := sorry

theorem numericals_monotonic_repeated_chars (s : String) (c : Char) :
  ∀ i j : String.Pos, i < j → 
  (s.get i = c ∧ s.get j = c) → 
  ((numericals s).get i).toNat ≤ ((numericals s).get j).toNat := sorry

theorem numericals_starts_with_one {s : String} (h : s ≠ "") :
  ∃ p : String.Pos, (numericals s).get p = '1' := sorry

/-
info: '1112111121311'
-/
-- #guard_msgs in
-- #eval numericals "Hello, World!"

/-
info: '123456789101112'
-/
-- #guard_msgs in
-- #eval numericals "aaaaaaaaaaaa"

/-
info: '11121122342'
-/
-- #guard_msgs in
-- #eval numericals "hello hello"

-- Apps difficulty: introductory
-- Assurance level: unguarded