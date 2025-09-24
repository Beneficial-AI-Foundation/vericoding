-- <vc-preamble>
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)

theorem Find_spec_satisfied (a: Array Int) (key: Int) (h_precond : Find_precond (a) (key)) :
    Find_postcond (a) (key) (Find (a) (key) h_precond) h_precond := by
  sorry
-- </vc-theorems>