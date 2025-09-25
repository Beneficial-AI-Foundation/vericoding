-- <vc-preamble>
@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0
-- </vc-helpers>

-- <vc-definitions>
def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)

theorem findFirstOdd_spec_satisfied (a: Array Int) (h_precond : findFirstOdd_precond (a)) :
    findFirstOdd_postcond (a) (findFirstOdd (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>