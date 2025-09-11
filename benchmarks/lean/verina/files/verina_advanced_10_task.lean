-- <vc-preamble>
import Mathlib.Data.Nat.Prime.Defs

@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  primes.all (fun p => Nat.Prime p)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findExponents (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) : List (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) (h_precond : findExponents_precond (n) (primes)) : Prop :=
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))

theorem findExponents_spec_satisfied (n: Nat) (primes: List Nat) (h_precond : findExponents_precond (n) (primes)) :
    findExponents_postcond (n) (primes) (findExponents (n) (primes) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "n": 6,
            "primes": "[6]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "n": 6,
            "primes": "[2, 3]"
        },
        "expected": "[(2, 1), (3, 1)]",
        "unexpected": [
            "[(1, 2), (2, 3)]",
            "[(2, 1), (3, 2)]"
        ]
    },
    {
        "input": {
            "n": 6285195213566005335561053533150026217291776,
            "primes": "[2, 3, 5]"
        },
        "expected": "[(2, 55), (3, 55), (5, 0)]",
        "unexpected": [
            "[(2, 2), (3, 55), (5, 59)]",
            "[(2, 55), (3, 55), (7, 0)]"
        ]
    },
    {
        "input": {
            "n": 360,
            "primes": "[2, 3, 5]"
        },
        "expected": "[(2, 3), (3, 2), (5, 1)]",
        "unexpected": [
            "[(2, 3), (3, 2), (5, 0)]",
            "[(2, 3), (3, 2), (7, 5)]"
        ]
    },
    {
        "input": {
            "n": 18903812908,
            "primes": "[2, 43, 823, 133543]"
        },
        "expected": "[(2, 2), (43, 1), (823, 1), (133543, 1)]",
        "unexpected": [
            "[(2, 2), (43, 4), (823, 0), (133543, 1)]",
            "[(2, 2), (43, 1), (823, 2)]"
        ]
    },
    {
        "input": {
            "n": 114514,
            "primes": "[2, 31, 1847]"
        },
        "expected": "[(2, 1), (31, 1), (1847, 1)]",
        "unexpected": [
            "[(2, 1), (31, 1), (1847, 0)]",
            "[(2, 1), (33, 1), (1847, 1)]"
        ]
    },
    {
        "input": {
            "n": 20241147794175,
            "primes": "[3, 5, 7, 11, 31, 47]"
        },
        "expected": "[(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (47, 3)]",
        "unexpected": [
            "[(0, 77), (17, 7)]",
            "[(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (33, 2)]"
        ]
    }
]
-/