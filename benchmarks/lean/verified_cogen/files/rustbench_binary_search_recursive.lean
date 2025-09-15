-- <vc-preamble>
@[reducible, simp]
def binarySearchRecursive_precond (v : Array Int) (elem : Int) (c : Nat) (f : Nat) :=
  v.size ≤ 100000 ∧ 
  (∀ i j, i < j ∧ j < v.size → v[i]! ≤ v[j]!) ∧
  c ≤ f + 1 ∧ f + 1 ≤ v.size ∧
  (∀ k, k < c → v[k]! ≤ elem) ∧
  (∀ k, f < k ∧ k < v.size → v[k]! > elem)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()