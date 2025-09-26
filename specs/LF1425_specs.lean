-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_string (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input (s : String) (h : s.length > 0) :
  (find_smallest_string s).length = s.length :=
sorry

theorem output_has_same_characters (s : String) (h : s.length > 0) :
  (find_smallest_string s).toList.sorted = s.toList.sorted :=
sorry

theorem output_lexicographically_smaller_or_equal (s : String) (h : s.length > 0) :
  find_smallest_string s ≤ s :=
sorry

theorem result_is_minimal_rearrangement (s : String) (h : s.length > 0)
    (i : Nat) (h1 : i < s.length)
    (j : Nat) (h2 : j ≤ s.length - 1) :
  let c := s.data.get ⟨i, h1⟩
  let remaining := (s.take i) ++ (s.drop (i + 1))
  let candidate := (remaining.take j) ++ String.mk [c] ++ (remaining.drop j)
  find_smallest_string s ≤ candidate :=
sorry

theorem sorted_string_is_minimal (s : String) (h : s.length > 0) :
  let sorted_s := String.mk (s.toList.sorted)
  find_smallest_string sorted_s = sorted_s :=
sorry

/-
info: 'ADCB'
-/
-- #guard_msgs in
-- #eval find_smallest_string "DCBA"

/-
info: 'XYYZZZZ'
-/
-- #guard_msgs in
-- #eval find_smallest_string "XYZZYZZ"

/-
info: 'ABC'
-/
-- #guard_msgs in
-- #eval find_smallest_string "ABC"
-- </vc-theorems>