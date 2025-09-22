-- <vc-preamble>
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)

theorem iter_copy_spec_satisfied (s: Array Int) (h_precond : iter_copy_precond (s)) :
    iter_copy_postcond (s) (iter_copy (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>