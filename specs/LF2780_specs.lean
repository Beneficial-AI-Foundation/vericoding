-- <vc-preamble>
def blocks_to_collect (level : Nat) : BlockCount :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def square (n : Nat) : Nat := n * n

def goldCalc (level : Nat) : Nat := 
  match level with
  | 0 => 0
  | n + 1 => 
    if (n % 4 = 0) then
      square (n + n + 3) + goldCalc n
    else
      goldCalc n
-- </vc-definitions>

-- <vc-theorems>
theorem blocks_total_is_sum_of_others (level : Nat) :
  let result := blocks_to_collect level
  result.total = result.gold + result.diamond + result.emerald + result.iron :=
sorry

theorem values_are_nonnegative (level : Nat) :
  let result := blocks_to_collect level
  result.total ≥ 0 ∧ result.gold ≥ 0 ∧ result.diamond ≥ 0 ∧ result.emerald ≥ 0 ∧ result.iron ≥ 0 :=
sorry

theorem gold_blocks_pattern (level : Nat) :
  let result := blocks_to_collect level
  result.gold = goldCalc level :=
sorry

/-
info: {'total': 9, 'gold': 9, 'diamond': 0, 'emerald': 0, 'iron': 0}
-/
-- #guard_msgs in
-- #eval blocks_to_collect 1

/-
info: {'total': 34, 'gold': 9, 'diamond': 25, 'emerald': 0, 'iron': 0}
-/
-- #guard_msgs in
-- #eval blocks_to_collect 2

/-
info: {'total': 83, 'gold': 9, 'diamond': 25, 'emerald': 49, 'iron': 0}
-/
-- #guard_msgs in
-- #eval blocks_to_collect 3
-- </vc-theorems>