-- <vc-preamble>
@[reducible, simp]
def unique_precond (a : Array Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()