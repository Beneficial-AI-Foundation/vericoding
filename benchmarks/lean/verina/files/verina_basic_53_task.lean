-- <vc-preamble>
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  2 * result = N * (N + 1)

theorem CalSum_spec_satisfied (N: Nat) (h_precond : CalSum_precond (N)) :
    CalSum_postcond (N) (CalSum (N) h_precond) h_precond := by
  sorry
-- </vc-theorems>