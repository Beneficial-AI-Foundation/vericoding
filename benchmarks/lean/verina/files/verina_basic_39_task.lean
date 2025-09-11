-- <vc-preamble>
@[reducible, simp]
def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rotateRight (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def rotateRight_postcond (l : List Int) (n : Nat) (result: List Int) (h_precond : rotateRight_precond (l) (n)) :=
  result.length = l.length ∧
  (∀ i : Nat, i < l.length →
    let len := l.length
    let rotated_index := Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
    result[i]? = l[rotated_index]?)

theorem rotateRight_spec_satisfied (l: List Int) (n: Nat) (h_precond : rotateRight_precond (l) (n)) :
    rotateRight_postcond (l) (n) (rotateRight (l) (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "l": "[1, 2, 3, 4, 5]",
            "n": 2
        },
        "expected": [
            4,
            5,
            1,
            2,
            3
        ],
        "unexpected": [
            [
                5,
                1,
                2,
                3,
                4
            ],
            [
                3,
                4,
                5,
                1,
                2
            ]
        ]
    },
    {
        "input": {
            "l": "[1, 2, 3, 4, 5]",
            "n": 7
        },
        "expected": [
            4,
            5,
            1,
            2,
            3
        ],
        "unexpected": [
            [
                5,
                1,
                2,
                3,
                4
            ],
            [
                3,
                4,
                5,
                1,
                2
            ]
        ]
    },
    {
        "input": {
            "l": "[1, 2, 3, 4, 5]",
            "n": 0
        },
        "expected": [
            1,
            2,
            3,
            4,
            5
        ],
        "unexpected": [
            [
                5,
                1,
                2,
                3,
                4
            ],
            [
                4,
                5,
                1,
                2,
                3
            ]
        ]
    },
    {
        "input": {
            "l": "[]",
            "n": 2
        },
        "expected": [],
        "unexpected": [
            [
                0
            ],
            [
                42
            ]
        ]
    }
]
-/