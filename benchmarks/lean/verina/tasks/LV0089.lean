-- <vc-preamble>
@[reducible, simp]
def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) (h_precond : hasCommonElement_precond (a) (b)) :=
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result

theorem hasCommonElement_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    hasCommonElement_postcond (a) (b) (hasCommonElement (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>