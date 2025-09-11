-- <vc-preamble>
@[reducible, simp]
def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeIntervals (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : List (Prod Int Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def mergeIntervals_postcond (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : Prop :=
  -- Check that all original intervals are covered by some result interval
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))

  -- Check that no intervals in the result overlap
  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)

  covered ∧ noOverlap result

theorem mergeIntervals_spec_satisfied (intervals: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    mergeIntervals_postcond (intervals) (mergeIntervals (intervals) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "intervals": "[(1, 3), (2, 6), (8, 10), (15, 18)]"
        },
        "expected": "[(1, 6), (8, 10), (15, 18)]",
        "unexpected": [
            "[(1, 3), (2, 6), (15, 19)]"
        ]
    },
    {
        "input": {
            "intervals": "[(1, 4), (4, 5)]"
        },
        "expected": "[(1, 5)]",
        "unexpected": [
            "[(1, 4), (4, 5), (1, 6)]"
        ]
    },
    {
        "input": {
            "intervals": "[(1, 10), (2, 3), (4, 5)]"
        },
        "expected": "[(1, 10)]",
        "unexpected": [
            "[(2, 3), (4, 5), (1, 5)]"
        ]
    },
    {
        "input": {
            "intervals": "[(1, 2), (3, 4), (5, 6)]"
        },
        "expected": "[(1, 2), (3, 4), (5, 6)]",
        "unexpected": [
            "[(1, 4), (5, 6), (1, 6)]"
        ]
    },
    {
        "input": {
            "intervals": "[(5, 6), (1, 3), (2, 4)]"
        },
        "expected": "[(1, 4), (5, 6)]",
        "unexpected": [
            "[(1, 3), (2, 4), (1, 6)]"
        ]
    }
]
-/