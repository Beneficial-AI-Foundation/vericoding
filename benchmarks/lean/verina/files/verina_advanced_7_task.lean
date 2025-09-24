-- <vc-preamble>
@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0

theorem binaryToDecimal_spec_satisfied (digits: List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    binaryToDecimal_postcond (digits) (binaryToDecimal (digits) h_precond) h_precond := by
  sorry
-- </vc-theorems>