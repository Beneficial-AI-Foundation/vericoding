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

-- Test cases and examples
def main : IO Unit := pure ()