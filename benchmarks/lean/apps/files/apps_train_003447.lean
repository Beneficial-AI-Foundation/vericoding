-- <vc-preamble>
def reverse_it {α : Type} (x : α) : α := sorry

theorem reverse_it_string_length {s : String} : 
  String.length (reverse_it s) = String.length s := sorry

/- Helper function to get nth char of string -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getNth (s : String) (n : Nat) : Char := s.data.get! n

theorem reverse_it_string_reverses {s : String} {i : Nat} (h : i < String.length s) :
  getNth (reverse_it s) i = getNth s (String.length s - 1 - i) := sorry 

/- Type class for types that shouldn't be reversed -/
class NonString (α : Type)
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_it_non_string_identity {α : Type} [NonString α] (x : α) :
  reverse_it x = x := sorry

/-
info: 'olleH'
-/
-- #guard_msgs in
-- #eval reverse_it "Hello"

/-
info: 951413
-/
-- #guard_msgs in
-- #eval reverse_it 314159

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval reverse_it [1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded