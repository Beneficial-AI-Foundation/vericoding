@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  s.toList.length = p.toList.length

-- <vc-helpers>
-- </vc-helpers>

def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  sorry

@[reducible, simp]
def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))

theorem Match_spec_satisfied (s: String) (p: String) (h_precond : Match_precond (s) (p)) :
    Match_postcond (s) (p) (Match (s) (p) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "s": "abc",
            "p": "ac"
        }
    }
]
-- Tests
[
    {
        "input": {
            "s": "abc",
            "p": "a?c"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "hello",
            "p": "he?lo"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "world",
            "p": "w?rld"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "test",
            "p": "te?t"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "abc",
            "p": "abd"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/