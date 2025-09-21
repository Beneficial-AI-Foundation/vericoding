-- <vc-preamble>
@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def increasingTriplet_postcond (nums : List Int) (result: Bool) (h_precond : increasingTriplet_precond (nums)) : Prop :=
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))

theorem increasingTriplet_spec_satisfied (nums: List Int) (h_precond : increasingTriplet_precond (nums)) :
    increasingTriplet_postcond (nums) (increasingTriplet (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>