-- <vc-preamble>
@[reducible, simp]
def allCharactersSame_precond (charArr : Array Char) : Prop :=
  charArr.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allCharactersSame (charArr : Array Char) (h_precond : allCharactersSame_precond (charArr)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def allCharactersSame_postcond (charArr : Array Char) (result: Bool) (h_precond : allCharactersSame_precond (charArr)) : Prop :=
  (∀ i, 1 ≤ i ∧ i < charArr.size → charArr[0]! = charArr[i]!) ↔ result

theorem allCharactersSame_spec_satisfied (charArr: Array Char) (h_precond : allCharactersSame_precond (charArr)) :
    allCharactersSame_postcond (charArr) (allCharactersSame (charArr) h_precond) h_precond := by
  sorry
-- </vc-theorems>