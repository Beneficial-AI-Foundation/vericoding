import Mathlib
-- <vc-preamble>
@[reducible, simp]
def cubeSurfaceArea_precond (size : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma nat_sub_self' (n : Nat) : n - n = 0 := by simpa using Nat.sub_self n
-- </vc-helpers>

-- <vc-definitions>
def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  6 * size * size
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def cubeSurfaceArea_postcond (size : Nat) (result: Nat) (h_precond : cubeSurfaceArea_precond (size)) :=
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0

theorem cubeSurfaceArea_spec_satisfied (size: Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
  dsimp [cubeSurfaceArea_postcond, cubeSurfaceArea]
  constructor <;> simp
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "size": 3
        },
        "expected": 54,
        "unexpected": [
            27,
            48,
            60
        ]
    },
    {
        "input": {
            "size": 1
        },
        "expected": 6,
        "unexpected": [
            1,
            2,
            3
        ]
    },
    {
        "input": {
            "size": 10
        },
        "expected": 600,
        "unexpected": [
            100,
            500,
            610
        ]
    },
    {
        "input": {
            "size": 5
        },
        "expected": 150,
        "unexpected": [
            25,
            100,
            125
        ]
    },
    {
        "input": {
            "size": 2
        },
        "expected": 24,
        "unexpected": [
            8,
            16,
            20
        ]
    }
]
-/