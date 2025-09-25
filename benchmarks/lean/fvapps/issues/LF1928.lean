-- <vc-preamble>
def isLower (c : Char) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_min_string_after_shift (s : List Char) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input
  (s : List Char)
  (h : ∀ c ∈ s, isLower c) :
  (get_min_string_after_shift s).length = s.length :=
sorry

theorem output_has_valid_chars
  (s : List Char) 
  (h : ∀ c ∈ s, isLower c) :
  ∀ c ∈ get_min_string_after_shift s, isLower c :=
sorry

theorem output_changes_at_most_one_segment
  (s : List Char)
  (h : ∀ c ∈ s, isLower c) :
  let result := get_min_string_after_shift s
  let diff_positions := List.range s.length |>.filter (fun i => s.get! i ≠ result.get! i)
  diff_positions.length > 0 →
  (diff_positions.maximum?.getD 0) - (diff_positions.minimum?.getD 0) + 1 = diff_positions.length :=
sorry

theorem all_a_string
  (s : List Char)
  (h : ∀ c ∈ s, c = 'a')
  (h' : s.length > 0) :
  get_min_string_after_shift s = (List.replicate (s.length - 1) 'a') ++ ['z'] :=
sorry

theorem shifted_chars_decrease
  (s : List Char)
  (h : ∀ c ∈ s, isLower c) :
  let result := get_min_string_after_shift s
  let diff_positions := List.range s.length |>.filter (fun i => s.get! i ≠ result.get! i)
  ∀ i ∈ diff_positions,
    (s.get! i = 'a' → result.get! i = 'z') ∧
    (s.get! i ≠ 'a' → (result.get! i).toNat = (s.get! i).toNat - 1) :=
sorry

/-
info: 'bncdenqbdr'
-/
-- #guard_msgs in
-- #eval get_min_string_after_shift "codeforces"

/-
info: 'aaacaba'
-/
-- #guard_msgs in
-- #eval get_min_string_after_shift "abacaba"

/-
info: 'z'
-/
-- #guard_msgs in
-- #eval get_min_string_after_shift "a"
-- </vc-theorems>