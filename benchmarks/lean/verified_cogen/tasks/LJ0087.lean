-- <vc-preamble>
/- No precondition required for this function -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasCommonElement (list1 : Array Int) (list2 : Array Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasCommonElement_postcond (list1 : Array Int) (list2 : Array Int) (result: Bool) :=
  (∃ i j, i < list1.size ∧ j < list2.size ∧ list1[i]! = list2[j]!) ↔ result

theorem hasCommonElement_spec_satisfied (list1: Array Int) (list2: Array Int) :
    hasCommonElement_postcond (list1) (list2) (hasCommonElement (list1) (list2)) := by
  sorry
-- </vc-theorems>