-- <vc-preamble>
@[reducible, simp]
def smallestMissingNumber_precond (s : Array Int) :=
  (∀ i j, 0 ≤ i → i < j → j < s.size → s[i]! ≤ s[j]!) ∧ 
  (∀ i, 0 ≤ i → i < s.size → s[i]! ≥ 0) ∧ 
  s.size ≤ 100000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()