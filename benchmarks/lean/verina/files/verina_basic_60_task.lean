-- <vc-preamble>
@[reducible, simp]
def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- </vc-helpers>

-- <vc-definitions>
def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  result.all (fun x => isEven x && x ∈ arr) ∧
  List.Pairwise (fun (x, i) (y, j) => if i < j then arr.idxOf x ≤ arr.idxOf y else true) (result.toList.zipIdx)

theorem FindEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    FindEvenNumbers_postcond (arr) (FindEvenNumbers (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>