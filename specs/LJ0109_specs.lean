-- <vc-preamble>
-- Precondition definitions
@[reducible, simp]
def firstRepeatedChar_precond (str1 : Array Char) : Prop := True

-- Helper recursive function for counting frequency
def countFrequencyRcr : List Char → Char → Int
  | [], _ => 0
  | head :: tail, key => 
      countFrequencyRcr tail key + if head = key then 1 else 0

-- Check function for first repeated character specification
def checkFirstRepeatedChar (str1 : Array Char) (repeatedChar : Option (Nat × Char)) : Prop :=
  match repeatedChar with
  | some (idx, rpChar) => 
      (str1.toList.take idx).filter (fun x => countFrequencyRcr str1.toList x ≤ 1) = str1.toList.take idx ∧
      countFrequencyRcr str1.toList rpChar > 1
  | none => 
      ∀ k, k < str1.size → countFrequencyRcr str1.toList str1[k]! ≤ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstRepeatedChar (str1 : Array Char) (h_precond : firstRepeatedChar_precond str1) : Option (Nat × Char) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def firstRepeatedChar_postcond (str1 : Array Char) (repeatedChar : Option (Nat × Char)) (h_precond : firstRepeatedChar_precond str1) : Prop :=
  checkFirstRepeatedChar str1 repeatedChar

theorem firstRepeatedChar_spec_satisfied (str1 : Array Char) (h_precond : firstRepeatedChar_precond str1) :
    firstRepeatedChar_postcond str1 (firstRepeatedChar str1 h_precond) h_precond := by
  sorry
-- </vc-theorems>