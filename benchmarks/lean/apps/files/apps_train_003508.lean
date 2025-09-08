/-
# Task
 You are given a string `s`. Let's call its substring a group, if all letters in it are adjacent and the same(such as `"aa","bbb","cccc"`..). Let's call the substiring with 2 or more adjacent group a big group(such as `"aabb","bbccc"`...).

 Your task is to count the number of `big groups` in the given string.

# Example

 For `s = "ccccoodeffffiiighhhhhhhhhhttttttts"`, the result should be `3`.
 ```
The groups are "cccc", "oo", "ffff", "iii", "hhhhhhhhhh", "ttttttt"
The big groups are "ccccoo", "ffffiii", "hhhhhhhhhhttttttt", 
3 substrings altogether.```

 For `s = "gztxxxxxggggggggggggsssssssbbbbbeeeeeeehhhmmmmmmmitttttttlllllhkppppp"`, the result should be `2`.
 ```
The big groups are :
"xxxxxggggggggggggsssssssbbbbbeeeeeeehhhmmmmmmm"
and 
"tttttttlllll" ```

 For `s = "soooooldieeeeeer"`, the result should be `0`.

 There is no `big group` exist.

# Input/Output

 - `[input]` string `s`

  A string of lowercase Latin letters.

 - `[output]` an integer

  The number of big groups.
-/

-- <vc-helpers>
-- </vc-helpers>

def count_big_groups (s : String) : Nat :=
  sorry

theorem count_big_groups_nonnegative (s : String) :
  count_big_groups s ≥ 0 :=
  sorry

theorem single_chars_give_zero (s : String) :
  List.Nodup s.data → count_big_groups s = 0 :=
  sorry  

theorem single_repeat_gives_zero (s : String) (c : Char) :
  s.data = List.replicate s.length c → count_big_groups s = 0 :=
  sorry

theorem short_strings_give_zero (s : String) :
  s.length ≤ 3 → count_big_groups s = 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_big_groups "ccccoodeffffiiighhhhhhhhhhttttttts"

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_big_groups "soooooldieeeeeer"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_big_groups "gztxxxxxggggggggggggsssssssbbbbbeeeeeeehhhmmmmmmmitttttttlllllhkppppp"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible