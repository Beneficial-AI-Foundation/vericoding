-- <vc-preamble>
@[reducible, simp]
def toLowercase_precond (str1 : Array Char) := True

@[reducible, simp]
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

@[reducible, simp]
def shift32Spec (c : Char) : Char :=
  Char.ofNat ((c.toNat) + 32)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toLowercase (str1 : Array Char) (h_precond : toLowercase_precond (str1)) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def toLowercase_postcond (str1 : Array Char) (result: Array Char) (h_precond : toLowercase_precond (str1)) :=
  str1.size = result.size ∧ 
  (∀ i, i < str1.size → result[i]! = (if isUpperCase (str1[i]!) then shift32Spec (str1[i]!) else str1[i]!))

theorem toLowercase_spec_satisfied (str1: Array Char) (h_precond : toLowercase_precond (str1)) :
    toLowercase_postcond (str1) (toLowercase (str1) h_precond) h_precond := by
  sorry
-- </vc-theorems>