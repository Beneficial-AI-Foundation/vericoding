-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def balanced_string_split (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_split:
  balanced_string_split "" = 0 :=
  sorry

theorem single_char_split:
  balanced_string_split "R" = 0 ∧ balanced_string_split "L" = 0 :=
  sorry

theorem balanced_blocks_split (n: Nat) (h: n > 0):
  balanced_string_split (String.mk (List.join (List.replicate n ['R', 'R', 'L', 'L']))) = n :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval balanced_string_split "RLRRLLRLRL"

/-
info: 3
-/
-- #guard_msgs in
-- #eval balanced_string_split "RLLLLRRRLR"

/-
info: 1
-/
-- #guard_msgs in
-- #eval balanced_string_split "LLLLRRRR"
-- </vc-theorems>