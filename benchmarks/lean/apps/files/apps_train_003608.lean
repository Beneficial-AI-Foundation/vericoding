/-
If　`a = 1, b = 2, c = 3 ... z = 26`

Then `l + o + v + e = 54`

and `f + r + i + e + n + d + s + h + i + p = 108`

So `friendship` is twice stronger than `love` :-)

The input will always be in lowercase and never be empty.
-/

-- <vc-helpers>
-- </vc-helpers>

def words_to_marks (s : String) : Nat := sorry

theorem words_to_marks_positive (s : String) (h : s.length > 0) : 
  words_to_marks s > 0 := sorry

theorem words_to_marks_matches_manual_calc (s : String) :
  words_to_marks s = s.data.foldl (fun acc c => acc + (c.toNat - 'a'.toNat + 1)) 0 := sorry 

theorem words_to_marks_equals_total_letters (s : String) :
  words_to_marks s = s.data.foldl (fun acc c => acc + (c.toNat - 'a'.toNat + 1)) 0 := sorry

/-
info: 100
-/
-- #guard_msgs in
-- #eval words_to_marks "attitude"

/-
info: 75
-/
-- #guard_msgs in
-- #eval words_to_marks "friends"

/-
info: 66
-/
-- #guard_msgs in
-- #eval words_to_marks "family"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible