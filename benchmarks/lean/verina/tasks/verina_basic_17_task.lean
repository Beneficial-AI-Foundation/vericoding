-- <vc-preamble>
@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)
-- </vc-helpers>

-- <vc-definitions>
def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))

theorem toLowercase_spec_satisfied (s: String) (h_precond : toLowercase_precond (s)) :
    toLowercase_postcond (s) (toLowercase (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>