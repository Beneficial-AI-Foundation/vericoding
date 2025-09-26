import Mathlib
-- <vc-preamble>
@[reducible, simp]
def trapRainWater_precond (height : List Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def waterAt (height : List Nat) : List Nat :=
  List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)
-- </vc-helpers>

-- <vc-definitions>
def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  (waterAt height).foldl (· + ·) 0
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
  simp [trapRainWater, trapRainWater_postcond, waterAt]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "height": "[0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7
        ]
    },
    {
        "input": {
            "height": "[4, 2, 0, 3, 2, 5]"
        },
        "expected": 9,
        "unexpected": [
            8
        ]
    },
    {
        "input": {
            "height": "[1, 0, 2]"
        },
        "expected": 1,
        "unexpected": [
            0,
            2
        ]
    },
    {
        "input": {
            "height": "[3, 0, 1, 3, 0, 5]"
        },
        "expected": 8,
        "unexpected": [
            6
        ]
    },
    {
        "input": {
            "height": "[0, 1, 2, 3, 4, 5]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "height": "[]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    }
]
-/