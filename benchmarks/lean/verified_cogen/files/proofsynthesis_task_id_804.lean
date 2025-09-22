-- <vc-preamble>
@[reducible, simp]
def isEven (n : Nat) : Bool :=
  n % 2 = 0

@[reducible, simp]
def isProductEven_precond (arr : Array Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isProductEven (arr : Array Nat) (h_precond : isProductEven_precond (arr)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isProductEven_postcond (arr : Array Nat) (result: Bool) (h_precond : isProductEven_precond (arr)) :=
  result ↔ (∃ k, k < arr.size ∧ isEven (arr[k]!))

theorem isProductEven_spec_satisfied (arr: Array Nat) (h_precond : isProductEven_precond (arr)) :
    isProductEven_postcond (arr) (isProductEven (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>