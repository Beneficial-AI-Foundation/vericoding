-- <vc-preamble>
@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))

theorem hasOnlyOneDistinctElement_spec_satisfied (a: Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    hasOnlyOneDistinctElement_postcond (a) (hasOnlyOneDistinctElement (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>