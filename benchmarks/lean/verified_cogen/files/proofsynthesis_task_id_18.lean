-- <vc-preamble>
@[reducible, simp]
def removeChars_precond (str1 : Array Char) (str2 : Array Char) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeChars (str1 : Array Char) (str2 : Array Char) (h_precond : removeChars_precond str1 str2) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeChars_postcond (str1 : Array Char) (str2 : Array Char) (result : Array Char) (h_precond : removeChars_precond str1 str2) :=
  (∀ i, i < result.size → (str1.contains result[i]! ∧ ¬str2.contains result[i]!)) ∧
  (∀ i, i < str1.size → (str2.contains str1[i]! ∨ result.contains str1[i]!))

theorem removeChars_spec_satisfied (str1 : Array Char) (str2 : Array Char) (h_precond : removeChars_precond str1 str2) :
    removeChars_postcond str1 str2 (removeChars str1 str2 h_precond) h_precond := by
  sorry
-- </vc-theorems>