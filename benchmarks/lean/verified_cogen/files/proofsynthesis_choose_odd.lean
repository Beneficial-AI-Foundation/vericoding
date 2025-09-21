-- <vc-preamble>
@[reducible, simp]
def chooseOdd_precond (v : Array Nat) : Prop :=
  ∃ q : Nat, q < v.size ∧ v[q]! % 2 = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chooseOdd (v : Array Nat) (h_precond : chooseOdd_precond v) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def chooseOdd_postcond (v : Array Nat) (oddIndex : Nat) (h_precond : chooseOdd_precond v) : Prop :=
  oddIndex < v.size

theorem chooseOdd_spec_satisfied (v : Array Nat) (h_precond : chooseOdd_precond v) :
    chooseOdd_postcond v (chooseOdd v h_precond) h_precond := by
  sorry
-- </vc-theorems>