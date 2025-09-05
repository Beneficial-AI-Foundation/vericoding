/- 
-----Description-----
This task involves determining whether two integer values are equal. The goal is simply to compare the two provided numbers and indicate with a Boolean result whether they are the same.

-----Input-----
The input consists of two elements:
• a: An element of type Int.
• b: An element of type Int.

-----Output-----
The output is a Boolean:
• Returns true if a equals b.
• Returns false if a does not equal b.
-/

@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def Compare_postcond (a : Int) (b : Int) (result: Bool) (h_precond : Compare_precond (a) (b)) :=
  (a = b → result = true) ∧ (a ≠ b → result = false)

theorem Compare_spec_satisfied (a: Int) (b: Int) (h_precond : Compare_precond (a) (b)) :
    Compare_postcond (a) (b) (Compare (a) (b) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 1,
            "b": 1
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": 1,
            "b": 2
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/