-- <vc-preamble>
@[reducible, simp]
def SelectionSort_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a
-- </vc-helpers>

-- <vc-definitions>
def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList

theorem SelectionSort_spec_satisfied (a: Array Int) (h_precond : SelectionSort_precond (a)) :
    SelectionSort_postcond (a) (SelectionSort (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>