-- <vc-preamble>
@[reducible, simp]
def trapRainWater_precond (height : List Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def trapRainWater_postcond (height : List Nat) (result: Nat) (h_precond : trapRainWater_precond (height)) : Prop :=
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)

  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result

theorem trapRainWater_spec_satisfied (height: List Nat) (h_precond : trapRainWater_precond (height)) :
    trapRainWater_postcond (height) (trapRainWater (height) h_precond) h_precond := by
  sorry
-- </vc-theorems>