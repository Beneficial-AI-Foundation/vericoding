-- <vc-preamble>
@[reducible]
def smallestMissing_precond (l : List Nat) : Prop :=
  List.Pairwise (· < ·) l
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestMissing (l : List Nat) (h_precond : smallestMissing_precond (l)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def smallestMissing_postcond (l : List Nat) (result: Nat) (h_precond : smallestMissing_precond (l)) : Prop :=
  result ∉ l ∧ ∀ candidate : Nat, candidate < result → candidate ∈ l

theorem smallestMissing_spec_satisfied (l: List Nat) (h_precond : smallestMissing_precond (l)) :
    smallestMissing_postcond (l) (smallestMissing (l) h_precond) h_precond := by
  sorry
-- </vc-theorems>