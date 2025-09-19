-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def without_last {α : Type} (xs : List α) : List α := sorry

theorem without_last_length {α : Type} (xs : List α) (h : xs ≠ []) : 
  (without_last xs).length = xs.length - 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem without_last_preserves_order {α : Type} (xs : List α) (h : xs ≠ []) :
  without_last xs = xs.take (xs.length - 1) := sorry

theorem without_last_not_eq_self {α : Type} (xs : List α) (h : xs ≠ []) :
  without_last xs ≠ xs := sorry
-- </vc-theorems>