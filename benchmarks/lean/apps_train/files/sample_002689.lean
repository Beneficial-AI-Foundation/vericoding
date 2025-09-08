/-
When provided with a number between 0-9, return it in words.

Input :: 1

Output :: "One".

If your language supports it, try using a switch statement.
-/

-- <vc-helpers>
-- </vc-helpers>

def switch_it_up (n : Nat) : String := sorry

theorem switch_it_up_valid_format {n : Nat} (h : n < 10) :
  let result := switch_it_up n
  -- First character is uppercase
  result.length > 0 ∧
  Char.isUpper (result.front) ∧ 
  -- Rest are lowercase
  ∀ i : String.Pos, i.1 > 0 → Char.isLower (result.get i) := sorry

theorem switch_it_up_consistent {n : Nat} (h : n < 10) :
  switch_it_up n = switch_it_up n := sorry

theorem switch_it_up_injective {n1 n2 : Nat} (h1 : n1 < 10) (h2 : n2 < 10) :
  n1 ≠ n2 → switch_it_up n1 ≠ switch_it_up n2 := sorry

/-
info: 'Zero'
-/
-- #guard_msgs in
-- #eval switch_it_up 0

/-
info: 'Five'
-/
-- #guard_msgs in
-- #eval switch_it_up 5

/-
info: 'Nine'
-/
-- #guard_msgs in
-- #eval switch_it_up 9

-- Apps difficulty: introductory
-- Assurance level: unguarded