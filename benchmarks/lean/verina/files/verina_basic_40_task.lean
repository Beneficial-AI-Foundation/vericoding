/- 
-----Description-----
This task requires writing a Lean 4 method that finds the second-smallest number in an array of integers. The method should determine and return the number that is larger than the smallest element in the array. It is crucial that the input array remains unchanged after the computation.

-----Input-----
The input consists of:
s: An array of integers containing at least two elements.

-----Output-----
The output is an integer:
Returns the second-smallest number in the input array.

-----Note-----
- The input array is guaranteed to contain at least two elements and is non-null.
- It is assumed that there exist at least two distinct values in the array to ensure a unique second-smallest element.
- The original array must remain unmodified.
-/

@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  s.size > 1

-- <vc-helpers>
def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i
-- </vc-helpers>

def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)

theorem secondSmallest_spec_satisfied (s: Array Int) (h_precond : secondSmallest_precond (s)) :
    secondSmallest_postcond (s) (secondSmallest (s) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "s": "#[1]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "s": "#[5, 3, 1, 4, 2]"
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            4
        ]
    },
    {
        "input": {
            "s": "#[7, 2, 5, 3]"
        },
        "expected": 3,
        "unexpected": [
            2,
            5,
            7
        ]
    },
    {
        "input": {
            "s": "#[10, 20]"
        },
        "expected": 20,
        "unexpected": [
            10,
            30,
            25
        ]
    },
    {
        "input": {
            "s": "#[20, 10]"
        },
        "expected": 20,
        "unexpected": [
            10,
            30,
            15
        ]
    },
    {
        "input": {
            "s": "#[3, 1, 2]"
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            4
        ]
    }
]
-/
