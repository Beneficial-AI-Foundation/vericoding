-- <vc-preamble>
def BirdString := List Bird

def diffs : BirdString → BirdString → Nat
  | _, _ => sorry

def child : BirdString → BirdString → Bool
  | _, _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def grandchild : BirdString → BirdString → Bool 
  | _, _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diffs_upper_bound (s1 s2 : BirdString) : 
  diffs s1 s2 ≤ min (List.length s1) (List.length s2) :=
sorry

theorem diffs_equal_zero (s : BirdString) :
  diffs s s = 0 :=
sorry

theorem child_diffs_range (s1 s2 : BirdString) :
  child s1 s2 = true → 1 ≤ diffs s1 s2 ∧ diffs s1 s2 ≤ 2 :=
sorry

theorem not_child_outside_range (s1 s2 : BirdString) :
  (diffs s1 s2 > 2 ∨ diffs s1 s2 = 0) → child s1 s2 = false :=
sorry

theorem single_char_grandchild (b1 b2 : Bird) :
  grandchild [b1] [b2] = (b1 = b2) :=
sorry

theorem grandchild_diffs_range (s1 s2 : BirdString) :
  List.length s1 > 1 →
  grandchild s1 s2 = true →
  0 ≤ diffs s1 s2 ∧ diffs s1 s2 ≤ 4 :=
sorry

theorem not_grandchild_excess_diffs (s1 s2 : BirdString) :
  List.length s1 > 1 →
  diffs s1 s2 > 4 →
  grandchild s1 s2 = false :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval child "BWBWBW" "BWBWBB"

/-
info: True
-/
-- #guard_msgs in
-- #eval grandchild magpie1 "WWWWBB"

/-
info: False
-/
-- #guard_msgs in
-- #eval child magpie1 magpie3
-- </vc-theorems>