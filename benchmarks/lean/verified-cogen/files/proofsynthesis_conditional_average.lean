-- <vc-preamble>
@[reducible, simp]
def conditionalAverage_precond (vals_1 : Array UInt64) (vals_2 : Array UInt64) (conds_1 : Array Bool) (conds_2 : Array Bool) (avgs : Array UInt64) :=
  vals_1.size = vals_2.size ∧
  vals_1.size = conds_1.size ∧
  vals_1.size = conds_2.size ∧
  (∀ idx : Nat, idx < vals_1.size → conds_1[idx]! ∨ conds_2[idx]!) ∧
  (∀ idx : Nat, idx < vals_1.size → vals_1[idx]! < 1000) ∧
  (∀ idx : Nat, idx < vals_2.size → vals_2[idx]! < 1000)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()