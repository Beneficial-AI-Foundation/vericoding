/-
For every string, after every occurrence of `'and'` and `'but'`, insert the substring `'apparently'` directly after the occurrence.

If input does not contain 'and' or 'but', return the original string. If a blank string, return `''`.

If substring `'apparently'` is already directly after an `'and'` and/or `'but'`, do not add another. (Do not add duplicates).

# Examples:

Input 1 

    'It was great and I've never been on live television before but sometimes I don't watch this.'

Output 1

    'It was great and apparently I've never been on live television before but apparently sometimes I don't watch this.'

Input 2

    'but apparently'

Output 2

    'but apparently' 
(no changes because `'apparently'` is already directly after `'but'` and there should not be a duplicate.)

An occurrence of `'and'` and/or `'but'` only counts when it is at least one space separated. For example `'andd'` and `'bbut'` do not count as occurrences, whereas `'b but'` and `'and d'` does count.

reference that may help:
https://www.youtube.com/watch?v=rz5TGN7eUcM
-/

-- <vc-helpers>
-- </vc-helpers>

def apparently (s : String) : String := sorry

def String.occurrences (needle haystack : String) : Nat := sorry

theorem and_but_count_preserved (s : String) :
  let result := apparently s
  (s.occurrences "and" = result.occurrences "and") ∧ 
  (s.occurrences "but" = result.occurrences "but") := sorry

theorem length_increases_by_apparently (s : String) :
  let result := apparently s
  let len_diff := result.length - s.length
  len_diff ≥ 0 ∧ len_diff % 11 = 0 := sorry

theorem empty_input_unchanged (s : String) :
  s = "" ∨ s = " " ∨ s = "  " →
  apparently s = s := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval apparently "It was great and I"ve never been on live television before but sometimes I don"t watch this."

/-
info: expected2
-/
-- #guard_msgs in
-- #eval apparently "but apparently"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval apparently "but and apparently apparently apparently apparently"

-- Apps difficulty: introductory
-- Assurance level: unguarded