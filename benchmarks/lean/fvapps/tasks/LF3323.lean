-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution {α : Type} [BEq α] : List α → Bool
  | xs => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_matches_manual {α : Type} [BEq α] (xs : List α) :
  solution xs = ∃ i j : Nat, i < j ∧ j < xs.length ∧ xs[i]? = xs[j]? := by sorry

theorem empty_and_single_no_duplicates {α : Type} [BEq α] (xs : List α) :
  xs.length ≤ 1 → solution xs = false := by sorry

theorem all_same_has_duplicates {α : Type} [BEq α] (x : α) (n : Nat) :
  n ≥ 2 → solution (List.replicate n x) = true := by sorry

theorem order_independent {α : Type} [BEq α] (xs : List α) :
  solution xs = solution xs.reverse := by sorry
-- </vc-theorems>