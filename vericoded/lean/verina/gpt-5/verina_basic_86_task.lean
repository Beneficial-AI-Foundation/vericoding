import Mathlib
-- <vc-preamble>
@[reducible, simp]
def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  offset ≥ 0
-- </vc-preamble>

-- <vc-helpers>
def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b
-- </vc-helpers>

-- <vc-definitions>
def rotate (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  let n := a.size
if h0 : n = 0 then
  a
else
  Array.ofFn (fun i : Fin n =>
    let idx := (Int.ofNat (i : Nat) + offset) % (Int.ofNat n)
    a[Int.toNat idx]!)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) (h_precond : rotate_precond (a) (offset)) :=
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)

theorem rotate_spec_satisfied (a: Array Int) (offset: Int) (h_precond : rotate_precond (a) (offset)) :
    rotate_postcond (a) (offset) (rotate (a) (offset) h_precond) h_precond := by
  classical
unfold rotate_postcond rotate
by_cases h0 : a.size = 0
· simp [h0]
· constructor
  · simp [h0]
  · intro i hi
    simp [h0, hi]
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "offset": -1
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "offset": 2
        },
        "expected": "#[3, 4, 5, 1, 2]",
        "unexpected": [
            "#[1, 2, 3, 4, 5]",
            "#[2, 3, 4, 5, 1]"
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30, 40]",
            "offset": 1
        },
        "expected": "#[20, 30, 40, 10]",
        "unexpected": [
            "#[10, 20, 30, 40]",
            "#[40, 10, 20, 30]"
        ]
    },
    {
        "input": {
            "a": "#[]",
            "offset": 5
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[1]"
        ]
    },
    {
        "input": {
            "a": "#[7]",
            "offset": 0
        },
        "expected": "#[7]",
        "unexpected": [
            "#[0]",
            "#[8]"
        ]
    },
    {
        "input": {
            "a": "#[-1, -2, -3, -4]",
            "offset": 3
        },
        "expected": "#[-4, -1, -2, -3]",
        "unexpected": [
            "#[-1, -2, -3, -4]",
            "#[-3, -4, -1, -2]"
        ]
    },
    {
        "input": {
            "a": "#[5, 10, 15]",
            "offset": 5
        },
        "expected": "#[15, 5, 10]",
        "unexpected": [
            "#[5, 10, 15]",
            "#[10, 15, 5]"
        ]
    }
]
-/