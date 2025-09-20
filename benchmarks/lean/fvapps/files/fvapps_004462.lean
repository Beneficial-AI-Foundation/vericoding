-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distribution_of (golds : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem distribution_sums_to_total {golds : List Nat} (h : golds ≠ []) :
  distribution_of golds = [a, b] →
  a + b = golds.foldl (init := 0) (· + ·) := by
  sorry

theorem distribution_returns_two_elements {golds : List Nat} (h : golds ≠ []) :
  ∃ a b, distribution_of golds = [a, b] := by
  sorry

theorem original_list_unchanged {golds : List Nat} (h : golds ≠ []) :
  let original := golds
  let _ := distribution_of golds
  golds = original := by
  sorry
-- </vc-theorems>