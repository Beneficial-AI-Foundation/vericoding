-- <vc-preamble>
@[reducible, simp]
def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  intervals.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxCoverageAfterRemovingOne (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxCoverageAfterRemovingOne_postcond (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Prop :=
  ∃ i < intervals.length,
    let remaining := List.eraseIdx intervals i
    let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
    let merged := sorted.foldl (fun acc curr =>
      match acc with
      | [] => [curr]
      | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
    ) []
    let cov := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
    result = cov ∧
    ∀ j < intervals.length,
      let rem_j := List.eraseIdx intervals j
      let sort_j := List.mergeSort rem_j (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged_j := sort_j.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let cov_j := merged_j.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      cov ≥ cov_j

theorem maxCoverageAfterRemovingOne_spec_satisfied (intervals: List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    maxCoverageAfterRemovingOne_postcond (intervals) (maxCoverageAfterRemovingOne (intervals) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "intervals": "[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "intervals": "[(1, 3), (2, 5), (6, 8)]"
        },
        "expected": 5,
        "unexpected": [
            4,
            6
        ]
    },
    {
        "input": {
            "intervals": "[(1, 4), (2, 6), (8, 10), (9, 12)]"
        },
        "expected": 8,
        "unexpected": [
            7,
            6
        ]
    },
    {
        "input": {
            "intervals": "[(1, 2), (2, 3), (3, 4)]"
        },
        "expected": 2,
        "unexpected": [
            3
        ]
    },
    {
        "input": {
            "intervals": "[(1, 10), (2, 3), (4, 5)]"
        },
        "expected": 9,
        "unexpected": [
            7,
            10
        ]
    },
    {
        "input": {
            "intervals": "[(5, 6), (1, 2), (3, 4)]"
        },
        "expected": 2,
        "unexpected": [
            5,
            3
        ]
    }
]
-/