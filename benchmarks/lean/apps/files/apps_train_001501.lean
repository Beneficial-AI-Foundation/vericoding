-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry

theorem pattern_length (k : Nat) (h: k > 0) :
  (generate_pattern k).length = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_identical_rows (k : Nat) (h: k > 0) :
  ∀ i j, i < (generate_pattern k).length → j < (generate_pattern k).length →
  ((generate_pattern k).get ⟨i, by sorry⟩) = ((generate_pattern k).get ⟨j, by sorry⟩) := sorry

theorem row_length (k : Nat) (h: k > 0) :
  ∀ row ∈ generate_pattern k, row.length = k := sorry

theorem alternating_digits (k : Nat) (h: k > 0) :
  ∀ i, i + 1 < k → 
  let pattern := (generate_pattern k).head!
  (pattern.data.get ⟨i, by sorry⟩) ≠ (pattern.data.get ⟨i + 1, by sorry⟩) := sorry

theorem first_digit_one (k : Nat) (h: k > 0) :
  let pattern := (generate_pattern k).head!
  (pattern.data.get ⟨0, by sorry⟩) = '1' := sorry

/-
info: ['1']
-/
-- #guard_msgs in
-- #eval generate_pattern 1

/-
info: ['10', '10']
-/
-- #guard_msgs in
-- #eval generate_pattern 2

/-
info: ['101', '101', '101']
-/
-- #guard_msgs in
-- #eval generate_pattern 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded