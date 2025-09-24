-- <vc-preamble>
@[reducible, simp]
def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSublist_postcond (sub : List Int) (main : List Int) (result: Bool) (h_precond : isSublist_precond (sub) (main)) :=
  (∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length) ↔ result

theorem isSublist_spec_satisfied (sub: List Int) (main: List Int) (h_precond : isSublist_precond (sub) (main)) :
    isSublist_postcond (sub) (main) (isSublist (sub) (main) h_precond) h_precond := by
  sorry
-- </vc-theorems>