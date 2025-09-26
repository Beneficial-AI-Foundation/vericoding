import Mathlib
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
-- LLM HELPER
lemma bool_ite_le_one (b : Bool) : (if b then (1 : Nat) else 0) ≤ 1 := by
  cases b <;> simp

-- LLM HELPER
lemma countUppercaseRecursively_le_length (L : List Char) :
    countUppercaseRecursively L ≤ L.length := by
  induction L with
  | nil =>
      simp [countUppercaseRecursively]
  | cons c cs ih =>
      have h1 : (if isUpperCase c then (1 : Nat) else 0) ≤ 1 :=
        bool_ite_le_one (isUpperCase c)
      have h2 :
          countUppercaseRecursively cs + (if isUpperCase c then (1 : Nat) else 0)
          ≤ countUppercaseRecursively cs + 1 :=
        Nat.add_le_add_left h1 _
      have h3 : countUppercaseRecursively cs + 1 ≤ cs.length + 1 :=
        Nat.add_le_add_right ih 1
      simpa [countUppercaseRecursively] using le_trans h2 h3
-- </vc-helpers>

-- <vc-definitions>
def countUppercase (text : Array Char) (h_precond : countUppercase_precond text) : Nat :=
  countUppercaseRecursively text.toList
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countUppercase_postcond (text : Array Char) (count : Nat) (h_precond : countUppercase_precond text) : Prop :=
  count ≤ text.size ∧ countUppercaseRecursively text.toList = count

theorem countUppercase_spec_satisfied (text : Array Char) (h_precond : countUppercase_precond text) :
    countUppercase_postcond text (countUppercase text h_precond) h_precond := by
  constructor
  ·
    have hlen : text.toList.length = text.size := by
      simpa using Array.size_toList (a := text)
    have hbase : countUppercaseRecursively text.toList ≤ text.toList.length :=
      countUppercaseRecursively_le_length (text.toList)
    simpa [countUppercase, hlen] using hbase
  ·
    simp [countUppercase]
-- </vc-theorems>
