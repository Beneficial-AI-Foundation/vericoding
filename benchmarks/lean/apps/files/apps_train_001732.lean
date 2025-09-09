/-
There is a secret string which is unknown to you. Given a collection of random triplets from the string, recover the original string. 

A triplet here is defined as a sequence of three letters such that each letter occurs somewhere before the next in the given string. "whi" is a triplet for the string "whatisup".

As a simplification, you may assume that no letter occurs more than once in the secret string.

You can assume nothing about the triplets given to you other than that they are valid triplets and that they contain sufficient information to deduce the original string. In particular, this means that the secret string will never contain letters that do not occur in one of the triplets given to you.
-/

def recoverSecret (triplets : List (List Char)) : String := sorry

def isConsistentWithTriplets (result : String) (triplets : List (List Char)) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def containsAllChars (result : String) (triplets : List (List Char)) : Bool := sorry

theorem recoverSecret_produces_string (triplets : List (List Char)) :
  String.length (recoverSecret triplets) > 0 := sorry

theorem recoverSecret_contains_all_chars (triplets : List (List Char)) : 
  containsAllChars (recoverSecret triplets) triplets = true := sorry

theorem recoverSecret_consistent_with_triplets (triplets : List (List Char)) :
  isConsistentWithTriplets (recoverSecret triplets) triplets = true := sorry

theorem recoverSecret_basic_case :
  recoverSecret [['a', 'b', 'c'], ['a', 'c', 'd']] = "abcd" := sorry

theorem recoverSecret_complex_case :
  recoverSecret [
    ['t','u','p'], 
    ['w','h','i'],
    ['t','s','u'],
    ['a','t','s'],
    ['h','a','p'],
    ['t','i','s'],
    ['w','h','s']
  ] = "whatisup" := sorry

/-
info: 'whatisup'
-/
-- #guard_msgs in
-- #eval recoverSecret [["t", "u", "p"], ["w", "h", "i"], ["t", "s", "u"], ["a", "t", "s"], ["h", "a", "p"], ["t", "i", "s"], ["w", "h", "s"]]

/-
info: 'abcd'
-/
-- #guard_msgs in
-- #eval recoverSecret [["a", "b", "c"], ["a", "c", "d"]]

/-
info: 'great'
-/
-- #guard_msgs in
-- #eval recoverSecret [["g", "r", "t"], ["e", "a", "t"]]

-- Apps difficulty: interview
-- Assurance level: unguarded