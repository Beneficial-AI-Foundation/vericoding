-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vowel_back (s : String) : String := sorry

theorem vowel_back_same_length (s : String) 
  (h : s.all (fun c => 'a' ≤ c ∧ c ≤ 'z')) 
  (h2 : s.length > 0) : 
  (vowel_back s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vowel_back_lowercase_letters (s : String)
  (h : s.all (fun c => 'a' ≤ c ∧ c ≤ 'z'))
  (h2 : s.length > 0) :
  (vowel_back s).all (fun c => 'a' ≤ c ∧ c ≤ 'z') := sorry

theorem vowel_back_deterministic (s : String)
  (h : s.all (fun c => 'a' ≤ c ∧ c ≤ 'z'))
  (h2 : s.length > 0) :
  vowel_back s = vowel_back s := sorry

theorem vowel_back_consistent_mapping (s : String)
  (h : s.all (fun c => 'a' ≤ c ∧ c ≤ 'z'))
  (h2 : s.length > 0) :
  ∀ i j, i < s.length → j < s.length → 
  s.data[i]? = s.data[j]? → 
  (vowel_back s).data[i]? = (vowel_back s).data[j]? := sorry

/-
info: 'tabtbvba'
-/
-- #guard_msgs in
-- #eval vowel_back "testcase"

/-
info: 'bnaafvab'
-/
-- #guard_msgs in
-- #eval vowel_back "codewars"

/-
info: 'agvvyuatabtqaaa'
-/
-- #guard_msgs in
-- #eval vowel_back "exampletesthere"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded