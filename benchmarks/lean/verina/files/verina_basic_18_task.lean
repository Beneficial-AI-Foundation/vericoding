-- <vc-preamble>
@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0

theorem sumOfDigits_spec_satisfied (n: Nat) (h_precond : sumOfDigits_precond (n)) :
    sumOfDigits_postcond (n) (sumOfDigits (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>