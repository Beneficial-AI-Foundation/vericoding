-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distinctEchoSubstrings (text: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_type_and_range (text: String)
  (h: text.length > 0) :
  distinctEchoSubstrings text ≥ 0 ∧ 
  distinctEchoSubstrings text ≤ text.length / 2 :=
  sorry

theorem repeating_char (text: String) 
  (h1: text.length > 0)
  (h2: ∀ (i j : String.Pos), text.get i = text.get j) :
  distinctEchoSubstrings text = text.length / 2 :=
  sorry

theorem doubled_string (text: String)
  (h: text.length > 0) :
  distinctEchoSubstrings (text ++ text) ≥ 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval distinct_echo_substrings "abcabcabc"

/-
info: 2
-/
-- #guard_msgs in
-- #eval distinct_echo_substrings "leetcodeleetcode"

/-
info: 1
-/
-- #guard_msgs in
-- #eval distinct_echo_substrings "aaa"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded