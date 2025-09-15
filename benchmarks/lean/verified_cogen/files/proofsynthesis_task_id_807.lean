-- <vc-preamble>
@[reducible, simp]
def findFirstOdd_precond (arr : Array UInt32) : Prop := True

@[reducible, simp]
def checkFindFirstOdd (arr : Array UInt32) (index : Option Nat) : Prop :=
  match index with
  | some idx => 
    (∀ i, i < idx → arr[i]! % 2 = 0) ∧ arr[idx]! % 2 ≠ 0
  | none => 
    ∀ k, k < arr.size → arr[k]! % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()