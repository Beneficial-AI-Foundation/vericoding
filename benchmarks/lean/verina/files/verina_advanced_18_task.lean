@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  True

-- <vc-helpers>
def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0
-- </vc-helpers>

def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  sorry

@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))

theorem isArmstrong_spec_satisfied (n: Nat) (h_precond : isArmstrong_precond (n)) :
    isArmstrong_postcond (n) (isArmstrong (n) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 0
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 1
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 10
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 153
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 9474
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 9475
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/