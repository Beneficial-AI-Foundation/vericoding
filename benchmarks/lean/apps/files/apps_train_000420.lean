-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distinctSubseqCount (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds {s : String} (h : s.length > 0) : 
  let result := distinctSubseqCount s
  0 ≤ result ∧ result < 10^9 + 7 :=
  sorry

theorem all_same_char {s : String} (h1 : s.length > 0) 
  (h2 : ∀ i : String.Pos, s.get i = 'a') :
  distinctSubseqCount s = s.length :=
  sorry

theorem length_property {s : String} (h : s.length > 0) :
  distinctSubseqCount s ≥ s.length :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval distinct_subseq_count "abc"

/-
info: 6
-/
-- #guard_msgs in
-- #eval distinct_subseq_count "aba"

/-
info: 3
-/
-- #guard_msgs in
-- #eval distinct_subseq_count "aaa"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded