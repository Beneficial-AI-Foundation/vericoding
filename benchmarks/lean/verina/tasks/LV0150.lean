-- <vc-preamble>
@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  ∃ i, i < a.size ∧ P (a[i]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) (h_precond : LinearSearch3_precond (a) (P)) :=
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))

theorem LinearSearch3_spec_satisfied (a: Array Int) (P: Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    LinearSearch3_postcond (a) (P) (LinearSearch3 (a) (P) h_precond) h_precond := by
  sorry
-- </vc-theorems>