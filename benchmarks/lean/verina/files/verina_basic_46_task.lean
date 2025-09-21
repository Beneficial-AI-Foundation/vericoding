-- <vc-preamble>
@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))

theorem lastPosition_spec_satisfied (arr: Array Int) (elem: Int) (h_precond : lastPosition_precond (arr) (elem)) :
    lastPosition_postcond (arr) (elem) (lastPosition (arr) (elem) h_precond) h_precond := by
  sorry
-- </vc-theorems>