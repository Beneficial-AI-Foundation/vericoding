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
-- </vc-theorems>