-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort (l : List α) : List α :=
  sorry

def same (a b : List (List Int)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_reflexive (arr : List (List Int)) : same arr arr = true := by
  sorry

theorem same_symmetric (arr_a arr_b : List (List Int)) :
  (List.map List.sort arr_a).sort = (List.map List.sort arr_b).sort →
  same arr_a arr_b = true ∧ same arr_b arr_a = true := by
  sorry

theorem same_single_array (nums : List Int) :
  same [nums] [nums.reverse] = true := by
  sorry

theorem same_order_invariant (arr_a arr_b : List (List Int)) :
  (List.map List.sort arr_a).sort = (List.map List.sort arr_b).sort →
  same arr_a arr_b = true := by
  sorry
-- </vc-theorems>