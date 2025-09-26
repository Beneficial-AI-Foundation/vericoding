import Mathlib
-- <vc-preamble>
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none
@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper lemmas required for this development.
-- </vc-helpers>

-- <vc-definitions>
def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  match firstEvenOddIndices lst with
| some (ei, oi) => lst[ei]! * lst[oi]!
| none => 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True

theorem findProduct_spec_satisfied (lst: List Int) (h_precond : findProduct_precond (lst)) :
    findProduct_postcond (lst) (findProduct (lst) h_precond) h_precond := by
  cases h : firstEvenOddIndices lst with
| none =>
    simp [findProduct_postcond, findProduct, h]
| some p =>
    rcases p with ⟨ei, oi⟩
    simp [findProduct_postcond, findProduct, h]
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "lst": "[2]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "lst": "[2, 3, 4, 5]"
        },
        "expected": 6,
        "unexpected": [
            8,
            0,
            10
        ]
    },
    {
        "input": {
            "lst": "[2, 4, 3, 6]"
        },
        "expected": 6,
        "unexpected": [
            8,
            0,
            24
        ]
    },
    {
        "input": {
            "lst": "[1, 2, 5, 4]"
        },
        "expected": 2,
        "unexpected": [
            5,
            0,
            10
        ]
    }
]
-/