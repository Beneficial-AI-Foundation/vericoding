-- <vc-helpers>
-- </vc-helpers>

def shorter_reverse_longer (a b : String) : String := sorry

def reverse (s : String) : String := sorry

theorem shorter_reverse_longer_length (a b : String) : 
  let result := shorter_reverse_longer a b
  String.length result = 2 * min (String.length a) (String.length b) + max (String.length a) (String.length b)
  := sorry

theorem shorter_reverse_longer_empty_left (s : String) :
  shorter_reverse_longer "" s = reverse s := sorry

theorem shorter_reverse_longer_empty_right (s : String) :
  shorter_reverse_longer s "" = reverse s := sorry

/-
info: 'abcdtsrifabcd'
-/
-- #guard_msgs in
-- #eval shorter_reverse_longer "first" "abcd"

/-
info: 'bauollehbau'
-/
-- #guard_msgs in
-- #eval shorter_reverse_longer "hello" "bau"

/-
info: 'dcba'
-/
-- #guard_msgs in
-- #eval shorter_reverse_longer "" "abcd"

-- Apps difficulty: introductory
-- Assurance level: unguarded