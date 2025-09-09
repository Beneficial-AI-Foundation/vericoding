-- <vc-helpers>
-- </vc-helpers>

def scramble (text : String) (indices : List Int) : String := sorry

theorem scramble_length_preserved 
  (text : String) 
  (indices : List Int) 
  (h1 : text.length > 0) :
  (scramble text indices).length = text.length := sorry

theorem scramble_chars_same_sorted
  (text : String)
  (indices : List Int)
  (h1 : text.length > 0) :
  String.toList (scramble text indices) = String.toList text := sorry

/-
info: 'acdb'
-/
-- #guard_msgs in
-- #eval scramble "abcd" [0, 3, 1, 2]

/-
info: 'c0s3s1'
-/
-- #guard_msgs in
-- #eval scramble "sc301s" [4, 0, 3, 1, 5, 2]

/-
info: '5sblk'
-/
-- #guard_msgs in
-- #eval scramble "bskl5" [2, 1, 4, 3, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded