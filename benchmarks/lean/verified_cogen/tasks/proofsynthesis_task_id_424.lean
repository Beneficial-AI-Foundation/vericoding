-- <vc-preamble>
@[reducible, simp]
def extractRearChars_precond (s : Array (Array Char)) :=
  ∀ i, i < s.size → s[i]!.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def extractRearChars (s : Array (Array Char)) (h_precond : extractRearChars_precond (s)) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def extractRearChars_postcond (s : Array (Array Char)) (result: Array Char) (h_precond : extractRearChars_precond (s)) :=
  s.size = result.size ∧ (∀ i, i < s.size → result[i]! = s[i]![s[i]!.size - 1]!)

theorem extractRearChars_spec_satisfied (s: Array (Array Char)) (h_precond : extractRearChars_precond (s)) :
    extractRearChars_postcond (s) (extractRearChars (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>