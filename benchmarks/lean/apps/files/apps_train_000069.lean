-- <vc-preamble>
def min_replacements (n k : Nat) (s : String) : Nat :=
  sorry

def is_palindrome (s : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_char_count (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_replacements_nonneg (n k : Nat) (s : String) :
  min_replacements n k s ≥ 0 :=
  sorry

theorem min_replacements_bounded (n k : Nat) (s : String) :
  min_replacements n k s ≤ n :=
  sorry

theorem uniform_string_zero (n k : Nat) (s : String) :
  s = String.mk (List.replicate n 'a') →
  min_replacements n (min k n) s = 0 :=
  sorry

theorem min_replacements_type (n k : Nat) (s : String) :
  min_replacements n k s ≥ 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_replacements 6 2 "abaaba"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_replacements 6 3 "abaaba"

/-
info: 23
-/
-- #guard_msgs in
-- #eval min_replacements 36 9 "hippopotomonstrosesquippedaliophobia"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible