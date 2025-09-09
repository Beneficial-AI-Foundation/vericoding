/-
Given a string and an array of index numbers, return the characters of the string rearranged to be in the order specified by the accompanying array.

Ex:

scramble('abcd', [0,3,1,2]) -> 'acdb' 

The string that you will be returning back will have: 'a' at index 0, 'b' at index 3, 'c' at index 1, 'd' at index 2, because the order of those characters maps to their corisponding numbers in the index array. 

In other words, put the first character in the string at the index described by the first element of the array

You can assume that you will be given a string and array of equal length and both containing valid characters (A-Z, a-z, or 0-9).
-/

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