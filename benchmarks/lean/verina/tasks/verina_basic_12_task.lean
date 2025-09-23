-- <vc-preamble>
@[reducible, simp]
def cubeSurfaceArea_precond (size : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def cubeSurfaceArea_postcond (size : Nat) (result: Nat) (h_precond : cubeSurfaceArea_precond (size)) :=
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0

theorem cubeSurfaceArea_spec_satisfied (size: Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
  sorry
-- </vc-theorems>