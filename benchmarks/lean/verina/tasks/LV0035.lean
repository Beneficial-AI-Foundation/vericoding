-- <vc-preamble>
@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def majorityElement_postcond (xs : List Nat) (result: Nat) (h_precond : majorityElement_precond (xs)) : Prop :=
  let count := xs.count result
  count > xs.length / 2

theorem majorityElement_spec_satisfied (xs: List Nat) (h_precond : majorityElement_precond (xs)) :
    majorityElement_postcond (xs) (majorityElement (xs) h_precond) h_precond := by
  sorry
-- </vc-theorems>