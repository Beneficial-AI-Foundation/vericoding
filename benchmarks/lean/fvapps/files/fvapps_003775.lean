-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def match_arrays (arr1 : List α) (arr2 : List α) [DecidableEq α] : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem match_arrays_range {α : Type} [DecidableEq α] (arr1 arr2 : List α) :
  0 ≤ match_arrays arr1 arr2 ∧ match_arrays arr1 arr2 ≤ arr1.length :=
sorry

theorem match_arrays_counts_common {α : Type} [DecidableEq α] (arr1 arr2 : List α) :
  match_arrays arr1 arr2 = (arr1.filter (fun x => arr2.contains x)).length :=
sorry

theorem match_arrays_order_invariant {α : Type} [DecidableEq α] (arr1 arr2 : List α) :
  match_arrays arr1 arr2 = match_arrays arr1.reverse arr2.reverse :=
sorry

theorem match_arrays_empty_right {α : Type} [DecidableEq α] (arr1 : List α) :
  match_arrays arr1 [] = 0 :=
sorry

theorem match_arrays_empty_left {α : Type} [DecidableEq α] (arr2 : List α) :
  match_arrays [] arr2 = 0 :=
sorry

theorem match_arrays_self {α : Type} [DecidableEq α] (arr : List α) :
  match_arrays arr arr = arr.length :=
sorry
-- </vc-theorems>