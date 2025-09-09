def isDigit (c : Char) : Bool := sorry

def isNonZeroDigit (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def look_and_say_sequence (s : String) (n : Nat) : String := sorry

theorem sequence_preserves_digits (s : String) (n : Nat) 
  (h : ∀ c ∈ s.data, isNonZeroDigit c) :
  ∀ c ∈ (look_and_say_sequence s n).data, isDigit c := sorry

theorem sequence_length_monotonic (s : String) (n : Nat)
  (h : ∀ c ∈ s.data, isNonZeroDigit c) :
  (look_and_say_sequence s n).length ≤ (look_and_say_sequence s (n+1)).length := sorry  

theorem first_element_unchanged (s : String)
  (h : ∀ c ∈ s.data, isNonZeroDigit c) :
  look_and_say_sequence s 1 = s := sorry

theorem repeating_digits_pattern (s : String)
  (h : ∀ c ∈ s.data, isNonZeroDigit c) :
  let result := look_and_say_sequence s 2
  ∀ i < result.length / 2,
    ∃ (p1 p2 : String.Pos),
    isNonZeroDigit (result.get p1) ∧ 
    isDigit (result.get p2) := sorry

theorem known_repeating_sequence :
  look_and_say_sequence "22" 9 = look_and_say_sequence "22" 10 := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval look_and_say_sequence "1" 1

/-
info: '21'
-/
-- #guard_msgs in
-- #eval look_and_say_sequence "1" 3

/-
info: '111221'
-/
-- #guard_msgs in
-- #eval look_and_say_sequence "1" 5

/-
info: '22'
-/
-- #guard_msgs in
-- #eval look_and_say_sequence "22" 10

/-
info: '1114'
-/
-- #guard_msgs in
-- #eval look_and_say_sequence "14" 2

-- Apps difficulty: introductory
-- Assurance level: unguarded