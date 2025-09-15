-- <vc-preamble>
@[reducible, simp]
def uniqueBetter_precond (a : Array Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Main function placeholder -/
def main : IO Unit := return ()