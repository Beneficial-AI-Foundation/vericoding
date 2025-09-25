-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def winner : List Candidate → Option String := sorry

theorem invalid_candidate_count 
  {cs : List Candidate} : 
  cs.length ≠ 3 → winner cs = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_scores 
  {cs : List Candidate}
  (h_length : cs.length = 3)
  (h_invalid : ∃ c, c ∈ cs ∧ ∃ s, s ∈ c.scores ∧ ¬(s % 5 = 0 ∧ 5 ≤ s ∧ s ≤ 100)) :
  winner cs = none := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval len candidates

/-
info: 'Bill'
-/
-- #guard_msgs in
-- #eval winner [c1, c2, c3]

/-
info: False
-/
-- #guard_msgs in
-- #eval winner []

/-
info: 'Bill'
-/
-- #guard_msgs in
-- #eval winner [c1, c2, c3]
-- </vc-theorems>