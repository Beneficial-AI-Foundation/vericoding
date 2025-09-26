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
-- LLM HELPER
lemma if_one_zero_le_one (b : Bool) : (if b then 1 else 0) ≤ 1 := by
  cases b <;> simp

-- LLM HELPER
lemma countDigitsRecursively_le_length (seq : List Char) :
    countDigitsRecursively seq ≤ seq.length := by
  induction seq with
  | nil =>
    simp [countDigitsRecursively]
  | cons h t ih =>
    have hb : (if isDigit h then 1 else 0) ≤ 1 := if_one_zero_le_one (isDigit h)
    simpa [countDigitsRecursively, Nat.succ_eq_add_one] using
      Nat.add_le_add ih hb
-- </vc-helpers>

-- <vc-definitions>
def countDigits (text : Array Char) (h_precond : countDigits_precond text) : Nat :=
  countDigitsRecursively text.toList
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countDigits_postcond (text : Array Char) (count : Nat) (h_precond : countDigits_precond text) : Prop :=
  count ≤ text.size ∧ countDigitsRecursively text.toList = count

theorem countDigits_spec_satisfied (text : Array Char) (h_precond : countDigits_precond text) :
    countDigits_postcond text (countDigits text h_precond) h_precond := by
  constructor
  ·
    have hlen : text.toList.length = text.size := by
      simpa using Array.size_toList (a := text)
    have hle : countDigitsRecursively text.toList ≤ text.toList.length :=
      countDigitsRecursively_le_length _
    simpa [countDigits, hlen] using hle
  ·
    simp [countDigits]
-- </vc-theorems>
