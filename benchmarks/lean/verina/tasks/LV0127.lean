-- <vc-preamble>
@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
theorem eq_of_sub_zero_and_ge (a b : Int) : a = b → a - b = 0 ∧ a ≥ b := by
  omega
-- </vc-helpers>

-- <vc-definitions>
def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!
@[reducible, simp]
def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size

theorem arraySum_spec_satisfied (a: Array Int) (h_precond : arraySum_precond (a)) :
    arraySum_postcond (a) (arraySum (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>