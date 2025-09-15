-- <vc-preamble>
@[reducible, simp]
def removeAllGreater_precond (v : Array Int) (e : Int) : Prop :=
  ∀ k1 k2, 0 ≤ k1 → k1 < k2 → k2 < v.size → v[k1]! ≠ v[k2]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  pure ()