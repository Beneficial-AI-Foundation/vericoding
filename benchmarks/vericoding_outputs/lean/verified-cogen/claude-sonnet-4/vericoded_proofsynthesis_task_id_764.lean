import Mathlib
-- <vc-preamble>
/- Helper function to check if a character is a digit -/
def isDigit (c : Char) : Bool :=
  (c.val >= 48) ∧ (c.val <= 57)

/- Recursive function to count digits in a sequence of characters -/
def countDigitsRecursively (seq : List Char) : Nat :=
  match seq with
  | [] => 0
  | h :: t => countDigitsRecursively t + if isDigit h then 1 else 0
termination_by seq.length

@[reducible, simp]
def countDigits_precond (text : Array Char) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Convert array to list and use existing recursive function
def arrayCountDigits (arr : Array Char) : Nat :=
  countDigitsRecursively arr.toList

-- LLM HELPER: Lemma that counting digits is bounded by array size
lemma countDigitsRecursively_le_length (chars : List Char) : countDigitsRecursively chars ≤ chars.length := by
  induction chars with
  | nil => simp [countDigitsRecursively]
  | cons h t ih =>
    simp [countDigitsRecursively]
    split_ifs with h_digit
    · exact Nat.succ_le_succ ih
    · exact Nat.le_succ_of_le ih
-- </vc-helpers>

-- <vc-definitions>
def countDigits (text : Array Char) (h_precond : countDigits_precond text) : Nat :=
  arrayCountDigits text
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countDigits_postcond (text : Array Char) (count : Nat) (h_precond : countDigits_precond text) : Prop :=
  count ≤ text.size ∧ countDigitsRecursively text.toList = count

theorem countDigits_spec_satisfied (text : Array Char) (h_precond : countDigits_precond text) :
    countDigits_postcond text (countDigits text h_precond) h_precond := by
  unfold countDigits_postcond countDigits arrayCountDigits
  constructor
  · -- Prove count ≤ text.size
    have h1 : countDigitsRecursively text.toList ≤ text.toList.length := countDigitsRecursively_le_length text.toList
    rw [← List.size_toArray] at h1
    exact h1
  · -- Prove countDigitsRecursively text.toList = count
    rfl
-- </vc-theorems>

def main : IO Unit := return ()