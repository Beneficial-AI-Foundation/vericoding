-- <vc-preamble>
@[reducible, simp]
def remove_front_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc
-- </vc-helpers>

-- <vc-definitions>
def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)

theorem remove_front_spec_satisfied (a: Array Int) (h_precond : remove_front_precond (a)) :
    remove_front_postcond (a) (remove_front (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>