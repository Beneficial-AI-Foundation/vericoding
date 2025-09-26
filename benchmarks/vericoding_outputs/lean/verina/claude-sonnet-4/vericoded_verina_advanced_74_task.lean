import Mathlib
-- <vc-preamble>
import Std.Data.HashSet
open Std

@[reducible]
def solution_precond (nums : List Nat) : Prop :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Function to get subarray from index i to j (inclusive)
def getSubarray (nums : List Nat) (i j : Nat) : List Nat :=
  (nums.drop i).take (j - i + 1)

-- LLM HELPER: Function to count distinct elements in a list
def distinctCount (l : List Nat) : Nat :=
  let foldFn := fun (seen : List Nat) (x : Nat) =>
    if seen.elem x then seen else x :: seen
  let distinctElems := l.foldl foldFn []
  distinctElems.length

-- LLM HELPER: Square function
def square (n : Nat) : Nat := n * n
-- </vc-helpers>

-- <vc-definitions>
def solution (nums : List Nat) : Nat :=
  let n := nums.length
  List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
    let innerSum : Nat :=
      List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
        let j := i + d
        let subarr := getSubarray nums i j
        let count := distinctCount subarr
        currentInnerSum + square count
      ) 0
    outerSum + innerSum
  ) 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def solution_postcond (nums : List Nat) (result: Nat) : Prop :=
  let n := nums.length;

  let getSubarray_local := fun (i j : Nat) =>
    (nums.drop i).take (j - i + 1);

  let distinctCount_local := fun (l : List Nat) =>
    let foldFn := fun (seen : List Nat) (x : Nat) =>
      if seen.elem x then seen else x :: seen;
    let distinctElems := l.foldl foldFn [];
    distinctElems.length;

  let square_local := fun (n : Nat) => n * n;

  (1 <= n ∧ n <= 100 ∧ nums.all (fun x => 1 <= x ∧ x <= 100)) ->
  (
    result >= 0
    ∧
    let expectedSum : Nat :=
      List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
        let innerSum : Nat :=
          List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
            let j := i + d;
            let subarr := getSubarray_local i j;
            let count := distinctCount_local subarr;
            currentInnerSum + square_local count
          ) 0
        outerSum + innerSum
      ) 0;

    result = expectedSum
  )

theorem solution_spec_satisfied (nums: List Nat) :
    solution_postcond (nums) (solution (nums)) := by
  intro h
  constructor
  · -- Prove result >= 0
    apply Nat.zero_le
  · -- Prove result equals expected sum
    unfold solution
    simp only []
    -- The implementation directly matches the expectedSum computation
    -- since our helper functions are definitionally equal to the local ones
    rfl
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[]"
        }
    },
    {
        "input": {
            "nums": "[101]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[1]"
        },
        "expected": 1,
        "unexpected": [
            2
        ]
    },
    {
        "input": {
            "nums": "[1, 1, 1]"
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
            "nums": "[1, 2, 1]"
        },
        "expected": 15,
        "unexpected": [
            12
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 3, 4]"
        },
        "expected": 50,
        "unexpected": []
    },
    {
        "input": {
            "nums": "[1, 2, 2, 3, 1]"
        },
        "expected": 62,
        "unexpected": [
            1,
            2,
            2,
            3,
            1
        ]
    }
]
-/