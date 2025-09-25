-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : Array String := sorry

theorem generate_pattern_length (k : Nat) (h : k > 0) : 
  (generate_pattern k).size = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_pattern_numeric (k : Nat) (h : k > 0) :
  ∀ s ∈ (generate_pattern k).data, ∀ c ∈ s.data, c.isDigit := sorry

/-
info: ['1121', '1222']
-/
-- #guard_msgs in
-- #eval generate_pattern 2

/-
info: ['112131', '122232', '132333']
-/
-- #guard_msgs in
-- #eval generate_pattern 3

/-
info: ['11213141', '12223242', '13233343', '14243444']
-/
-- #guard_msgs in
-- #eval generate_pattern 4
-- </vc-theorems>