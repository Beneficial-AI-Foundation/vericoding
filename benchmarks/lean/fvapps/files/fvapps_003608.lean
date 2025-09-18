-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def words_to_marks (s : String) : Nat := sorry

theorem words_to_marks_positive (s : String) (h : s.length > 0) : 
  words_to_marks s > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible