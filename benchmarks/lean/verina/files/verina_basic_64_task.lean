-- <vc-preamble>
@[reducible, simp]
def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insert (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :=
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)

theorem insert_spec_satisfied (oline: Array Char) (l: Nat) (nl: Array Char) (p: Nat) (atPos: Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    insert_postcond (oline) (l) (nl) (p) (atPos) (insert (oline) (l) (nl) (p) (atPos) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
  {
    "input": {
        "oline": "#['a','b','c']",
        "l": 5,
        "nl": "#['X','Y']",
        "p": 3,
        "atPos": 2
    }
  }
]
-- Tests
[
    {
        "input": {
            "oline": "#['a','b','c','d','e']",
            "l": 5,
            "nl": "#['X','Y']",
            "p": 2,
            "atPos": 2
        },
        "expected": "#['a','b','X','Y','c','d','e']",
        "unexpected": [
            "#['a','b','X','Y','c','d']",
            "#['a','b','X','Y','c','d','f']",
            "#['a','X','b','Y','c','d','e']"
        ]
    },
    {
        "input": {
            "oline": "#['H','e','l','l','o']",
            "l": 5,
            "nl": "#['W','o','r','l','d']",
            "p": 5,
            "atPos": 0
        },
        "expected": "#['W','o','r','l','d','H','e','l','l','o']",
        "unexpected": [
            "#['H','e','l','l','o','W','o','r','l','d']",
            "#['W','o','r','l','d','H','e','l','l','o','!']",
            "#['W','o','r','l','d','W','o','r','l','d']"
        ]
    },
    {
        "input": {
            "oline": "#['L','e','a','n']",
            "l": 4,
            "nl": "#['4']",
            "p": 1,
            "atPos": 4
        },
        "expected": "#['L','e','a','n','4']",
        "unexpected": [
            "#['L','e','a','n']",
            "#['L','e','a','n',' ']",
            "#['4','L','e','a','n']"
        ]
    },
    {
        "input": {
            "oline": "#['T','e','s','t']",
            "l": 4,
            "nl": "#[]",
            "p": 0,
            "atPos": 2
        },
        "expected": "#['T','e','s','t']",
        "unexpected": [
            "#['T','e','s']",
            "#['T','s','t','e']",
            "#['t','e','s','T']"
        ]
    },
    {
        "input": {
            "oline": "#['1','2','3','4','5','6']",
            "l": 5,
            "nl": "#['a','b','c']",
            "p": 3,
            "atPos": 3
        },
        "expected": "#['1','2','3','a','b','c','4','5']",
        "unexpected": [
            "#['1','2','3','a','b','c','4','5','6']",
            "#['1','2','3','4','a','b','c','5','6']",
            "#['1','2','3','a','b','4','c','5','6']"
        ]
    }
]
-/