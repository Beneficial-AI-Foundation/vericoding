-- <vc-preamble>
@[reducible, simp]
def TestArrayElements_precond (a : Array Int) (j : Nat) : Prop :=
  j < a.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def TestArrayElements (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def TestArrayElements_postcond (a : Array Int) (j : Nat) (result: Array Int) (h_precond : TestArrayElements_precond (a) (j)) :=
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)

theorem TestArrayElements_spec_satisfied (a: Array Int) (j: Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    TestArrayElements_postcond (a) (j) (TestArrayElements (a) (j) h_precond) h_precond := by
  sorry
-- </vc-theorems>