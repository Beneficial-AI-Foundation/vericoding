-- <vc-preamble>
@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isOdd (n : Int) : Bool :=
  n % 2 == 1
-- </vc-helpers>

-- <vc-definitions>
def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))

theorem isOddAtIndexOdd_spec_satisfied (a: Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    isOddAtIndexOdd_postcond (a) (isOddAtIndexOdd (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>