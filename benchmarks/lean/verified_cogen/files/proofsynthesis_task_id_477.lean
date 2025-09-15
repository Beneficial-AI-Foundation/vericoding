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

#check toLowercase
#check toLowercase_spec_satisfied