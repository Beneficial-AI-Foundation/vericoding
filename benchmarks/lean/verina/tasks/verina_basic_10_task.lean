-- <vc-preamble>
@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result

theorem isGreater_spec_satisfied (n: Int) (a: Array Int) (h_precond : isGreater_precond (n) (a)) :
    isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>