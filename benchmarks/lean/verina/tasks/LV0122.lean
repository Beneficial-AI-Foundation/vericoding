-- <vc-preamble>
@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'
-- </vc-helpers>

-- <vc-definitions>
def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0

theorem countDigits_spec_satisfied (s: String) (h_precond : countDigits_precond (s)) :
    countDigits_postcond (s) (countDigits (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>