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

def main : IO Unit := pure ()