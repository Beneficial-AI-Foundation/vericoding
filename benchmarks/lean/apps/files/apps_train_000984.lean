-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry

theorem pattern_only_digits (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  let pattern := generate_pattern k
  ∀ row ∈ pattern, ∀ c ∈ row.data, '0' ≤ c ∧ c ≤ '9' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_first_row_starts_with_two (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  let pattern := generate_pattern k
  pattern.head!.data.head! = '2' := sorry

theorem pattern_rows_nonempty (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  let pattern := generate_pattern k
  ∀ row ∈ pattern, row.length > 0 := sorry

theorem pattern_base_cases :
  generate_pattern 1 = ["2"] ∧
  generate_pattern 2 = ["24", "68"] := sorry

/-
info: ['2']
-/
-- #guard_msgs in
-- #eval generate_pattern 1

/-
info: ['24', '68']
-/
-- #guard_msgs in
-- #eval generate_pattern 2

/-
info: ['246', '81012', '141618']
-/
-- #guard_msgs in
-- #eval generate_pattern 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded