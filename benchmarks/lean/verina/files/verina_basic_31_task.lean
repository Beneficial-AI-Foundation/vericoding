-- <vc-preamble>
@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)
-- </vc-helpers>

-- <vc-definitions>
def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))

theorem toUppercase_spec_satisfied (s: String) (h_precond : toUppercase_precond (s)) :
    toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>