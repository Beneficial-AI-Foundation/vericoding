/- 
-----Description-----
Given an integer array arr and a positive integer k, this task requires writing a Lean 4 method that finds the
maximum sum of a subarray of arr, such that the length of the subarray is divisible by k.
If the array is empty, or generally if there exists no subarray with length divisible by k,
the default return value should be 0.

-----Input-----
The input consists of:
arr: The array of integers.
k: An integer larger than 1.

-----Output-----
The output is an integer:
Returns the maximum positive integer x such that there exists a subarray where the sum equals x, and the length
of the subarray is divisible by k.
-/

@[reducible]
def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  k > 0

-- <vc-helpers>
-- </vc-helpers>

def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  sorry

@[reducible]
def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.sum)
  (result = 0 → subarraySums.length = 0) ∧
  (result ≠ 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))

theorem maxSubarraySumDivisibleByK_spec_satisfied (arr: Array Int) (k: Int) :
    maxSubarraySumDivisibleByK_postcond (arr) (k) (maxSubarraySumDivisibleByK (arr) (k)) := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "#[1, 2, 3, 4, 5]",
            "k": 2
        },
        "expected": 14,
        "unexpected": [
            9,
            5,
            15,
            10
        ]
    },
    {
        "input": {
            "arr": "#[1, -2, 3, -4, 5]",
            "k": 3
        },
        "expected": 4,
        "unexpected": [
            2,
            5,
            3
        ]
    },
    {
        "input": {
            "arr": "#[]",
            "k": 5
        },
        "expected": 0,
        "unexpected": [
            -1
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3, 4]",
            "k": 1
        },
        "expected": 10,
        "unexpected": [
            3,
            4,
            7,
            9
        ]
    },
    {
        "input": {
            "arr": "#[-2, 7, 1, 3]",
            "k": 2
        },
        "expected": 9,
        "unexpected": [
            8,
            11,
            7
        ]
    },
    {
        "input": {
            "arr": "#[-100, 0, 1]",
            "k": 5
        },
        "expected": 0,
        "unexpected": [
            1,
            -99
        ]
    },
    {
        "input": {
            "arr": "#[1999, 1, -1023, 12351, -9999]",
            "k": 2
        },
        "expected": 13328,
        "unexpected": [
            1999,
            12351,
            3329,
            2352
        ]
    }
]
-/