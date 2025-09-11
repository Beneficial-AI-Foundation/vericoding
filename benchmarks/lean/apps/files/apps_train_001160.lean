-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_log_validity (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_length_log_invalid {s : String} :
  s.length % 2 ≠ 0 → check_log_validity s = "no" :=
sorry

theorem identical_adjacent_chars_invalid {s : String} {i : Nat} :
  s.length % 2 = 0 →
  i < s.length →
  i % 2 = 0 →
  i + 1 < s.length →
  s.get ⟨i⟩ = s.get ⟨i + 1⟩ →
  check_log_validity s = "no" :=
sorry

theorem no_identical_pairs_valid {s : String} :
  s.length % 2 = 0 →
  (∀ i, i < s.length → i % 2 = 0 → i + 1 < s.length → s.get ⟨i⟩ ≠ s.get ⟨i + 1⟩) →
  check_log_validity s = "yes" :=
sorry

/-
info: 'yes'
-/
-- #guard_msgs in
-- #eval check_log_validity "AB"

/-
info: 'yes'
-/
-- #guard_msgs in
-- #eval check_log_validity "ABBA"

/-
info: 'no'
-/
-- #guard_msgs in
-- #eval check_log_validity "AA"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded