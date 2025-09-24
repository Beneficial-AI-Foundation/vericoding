-- <vc-preamble>
@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  -- if result = -1, then lst does not contain any duplicates
  (result = -1 → List.Nodup lst) ∧
  -- if result is not -1, then it is the first duplicate in lst
  (result ≠ -1 →
    lst.count result > 1 ∧
    (lst.filter (fun x => lst.count x > 1)).head? = some result
  )

theorem firstDuplicate_spec_satisfied (lst: List Int) (h_precond : firstDuplicate_precond (lst)) :
    firstDuplicate_postcond (lst) (firstDuplicate (lst) h_precond) h_precond := by
  sorry
-- </vc-theorems>