-- <vc-preamble>
@[reducible, simp]
def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))

theorem replaceChars_spec_satisfied (s: String) (oldChar: Char) (newChar: Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    replaceChars_postcond (s) (oldChar) (newChar) (replaceChars (s) (oldChar) (newChar) h_precond) h_precond := by
  sorry
-- </vc-theorems>