-- <vc-preamble>
/- Lean 4 version of last_position function for finding the last occurrence of an element in an array -/

@[reducible, simp]
def lastPosition_precond (a : Array Int) (elem : Int) :=
  0 < a.size ∧ a.size < 100000 ∧ (∃ i, i < a.size ∧ a[i]! = elem)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastPosition (a : Array Int) (elem : Int) (h_precond : lastPosition_precond a elem) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def lastPosition_postcond (a : Array Int) (elem : Int) (result: Nat) (h_precond : lastPosition_precond a elem) :=
  result < a.size ∧ (∀ i, result < i ∧ i < a.size → a[i]! ≠ elem) ∧ a[result]! = elem

theorem lastPosition_spec_satisfied (a: Array Int) (elem: Int) (h_precond : lastPosition_precond a elem) :
    lastPosition_postcond a elem (lastPosition a elem h_precond) h_precond := by
  sorry
-- </vc-theorems>