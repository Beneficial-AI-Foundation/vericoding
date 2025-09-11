-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_substrings_in_wraparound (s: String) : Nat := sorry

theorem output_always_positive (s: String) : 
  find_substrings_in_wraparound s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_min (s: String) :
  s.length ≥ 1 → find_substrings_in_wraparound s ≥ 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_substrings_in_wraparound "a"

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_substrings_in_wraparound "cac"

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_substrings_in_wraparound "zab"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible