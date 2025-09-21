-- <vc-preamble>
-- Helper functions for character case checking
def isLowerCase (c : Char) : Bool :=
  c.toNat ≥ 97 ∧ c.toNat ≤ 122

def isUpperCase (c : Char) : Bool :=
  c.toNat ≥ 65 ∧ c.toNat ≤ 90

def countUppercaseRecursively (seq : List Char) : Nat :=
  match seq with
  | [] => 0
  | c :: cs => countUppercaseRecursively cs + if isUpperCase c then 1 else 0

@[reducible, simp]
def countUppercase_precond (text : Array Char) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countUppercase (text : Array Char) (h_precond : countUppercase_precond text) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countUppercase_postcond (text : Array Char) (count : Nat) (h_precond : countUppercase_precond text) : Prop :=
  count ≤ text.size ∧ countUppercaseRecursively text.toList = count

theorem countUppercase_spec_satisfied (text : Array Char) (h_precond : countUppercase_precond text) :
    countUppercase_postcond text (countUppercase text h_precond) h_precond := by
  sorry
-- </vc-theorems>