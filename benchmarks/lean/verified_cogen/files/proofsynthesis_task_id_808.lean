-- <vc-preamble>
@[reducible, simp]
def containsK_precond (arr : Array Int) (k : Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsK (arr : Array Int) (k : Int) (h_precond : containsK_precond (arr) (k)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsK_postcond (arr : Array Int) (k : Int) (result: Bool) (h_precond : containsK_precond (arr) (k)) :=
  (∃ i : Nat, i < arr.size ∧ arr[i]! = k) ↔ result

theorem containsK_spec_satisfied (arr: Array Int) (k: Int) (h_precond : containsK_precond (arr) (k)) :
    containsK_postcond (arr) (k) (containsK (arr) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>