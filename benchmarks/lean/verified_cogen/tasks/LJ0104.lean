-- <vc-preamble>
/- Helper function to check if sub is a subrange of main starting at position i -/
def isSubrangeAt (main : List Int) (sub : List Int) (i : Int) : Bool :=
  if i < 0 ∨ i + sub.length > main.length then false
  else sub = (main.drop i.natAbs).take sub.length

@[reducible, simp]
def isSubArray_precond (main : Array Int) (sub : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubArray (main : Array Int) (sub : Array Int) (h_precond : isSubArray_precond main sub) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSubArray_postcond (main : Array Int) (sub : Array Int) (result: Bool) (h_precond : isSubArray_precond main sub) : Prop :=
  result = (∃ k, 0 ≤ k ∧ k ≤ (main.size : Int) - (sub.size : Int) ∧ isSubrangeAt main.toList sub.toList k)

theorem isSubArray_spec_satisfied (main: Array Int) (sub: Array Int) (h_precond : isSubArray_precond main sub) :
    isSubArray_postcond main sub (isSubArray main sub h_precond) h_precond := by
  sorry
-- </vc-theorems>