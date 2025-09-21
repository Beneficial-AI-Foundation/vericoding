-- <vc-preamble>
@[reducible, simp]
def replaceLastElement_precond (first : Array Int) (second : Array Int) : Prop :=
  first.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replaceLastElement (first : Array Int) (second : Array Int) (h_precond : replaceLastElement_precond first second) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replaceLastElement_postcond (first : Array Int) (second : Array Int) (replaced_list : Array Int) (h_precond : replaceLastElement_precond first second) : Prop :=
  replaced_list.toList = (first.toList.take (first.size - 1)) ++ second.toList

theorem replaceLastElement_spec_satisfied (first : Array Int) (second : Array Int) (h_precond : replaceLastElement_precond first second) :
    replaceLastElement_postcond first second (replaceLastElement first second h_precond) h_precond := by
  sorry
-- </vc-theorems>