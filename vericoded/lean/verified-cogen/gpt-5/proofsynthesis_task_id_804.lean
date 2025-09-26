import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isEven (n : Nat) : Bool :=
  n % 2 = 0

@[reducible, simp]
def isProductEven_precond (arr : Array Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- no helper lemmas needed
-- </vc-helpers>

-- <vc-definitions>
def isProductEven (arr : Array Nat) (h_precond : isProductEven_precond (arr)) : Bool :=
  if h : ∃ k, k < arr.size ∧ isEven (arr[k]!) then true else false
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isProductEven_postcond (arr : Array Nat) (result: Bool) (h_precond : isProductEven_precond (arr)) :=
  result ↔ (∃ k, k < arr.size ∧ isEven (arr[k]!))

theorem isProductEven_spec_satisfied (arr: Array Nat) (h_precond : isProductEven_precond (arr)) :
    isProductEven_postcond (arr) (isProductEven (arr) h_precond) h_precond := by
  classical
dsimp [isProductEven_postcond, isProductEven]
by_cases h : ∃ k, k < arr.size ∧ isEven (arr[k]!)
· simp [h]
· simp [h]
-- </vc-theorems>
