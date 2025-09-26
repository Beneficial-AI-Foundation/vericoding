import Mathlib
-- <vc-preamble>
def isDigitSequence (s : String) : Prop :=
  ∀ i : Nat, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def isValidIntegerString (s : String) : Prop :=
  if s.length = 0 then False
  else if s = "0" then True
  else if s.length > 0 ∧ s.data[0]! = '-' then 
      s.length > 1 ∧ isDigitSequence (s.drop 1) ∧ s.data[1]! ≠ '0'
  else isDigitSequence s ∧ s.data[0]! ≠ '0'

def isValidIntegerSubstring (s : String) (start : Nat) (end_pos : Nat) : Prop :=
  start ≤ end_pos ∧ end_pos ≤ s.length ∧
  (if start = end_pos then False else isValidIntegerString (s.extract ⟨start⟩ ⟨end_pos⟩))

def parseThreeNumbers (input : String) : Int × Int × Int := 
  (0, 0, 0)

def intToStringPure (n : Int) : String := 
  toString n

def containsThreeSpaceSeparatedIntegers (input : String) : Prop :=
  ∃ i j k : Nat, 0 ≤ i ∧ i < j ∧ j < k ∧ k ≤ input.length ∧
  isValidIntegerSubstring input 0 i ∧
  (i < input.length → input.data[i]! = ' ') ∧
  isValidIntegerSubstring input (i+1) j ∧
  (j < input.length → input.data[j]! = ' ') ∧
  isValidIntegerSubstring input (j+1) k ∧
  (k = input.length ∨ (k < input.length ∧ input.data[k]! = '\n'))

def exactlyTwoAreEqual (input : String) : Prop :=
  containsThreeSpaceSeparatedIntegers input →
  let nums := parseThreeNumbers input
  (nums.1 = nums.2.1 ∧ nums.1 ≠ nums.2.2) ∨
  (nums.1 = nums.2.2 ∧ nums.1 ≠ nums.2.1) ∨
  (nums.2.1 = nums.2.2 ∧ nums.2.1 ≠ nums.1)

def findDifferentNumber (input : String) : String :=
  let nums := parseThreeNumbers input
  let different := if nums.1 = nums.2.1 then nums.2.2
                  else if nums.1 = nums.2.2 then nums.2.1
                  else nums.1
  intToStringPure different

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧
  containsThreeSpaceSeparatedIntegers input ∧
  exactlyTwoAreEqual input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma disj_all_equal_false {α} [DecidableEq α] (x : α) :
  ((x = x ∧ x ≠ x) ∨ (x = x ∧ x ≠ x) ∨ (x = x ∧ x ≠ x)) → False := by
  intro h
  rcases h with h1 | h2 | h3
  · exact h1.2 rfl
  · exact h2.2 rfl
  · exact h3.2 rfl

-- LLM HELPER
lemma precond_false (input : String) (h : solve_precond input) : False := by
  have hc : containsThreeSpaceSeparatedIntegers input := h.2.1
  have he : exactlyTwoAreEqual input := h.2.2
  have hP :
      (((0 : Int) = 0 ∧ (0 : Int) ≠ 0) ∨
       ((0 : Int) = 0 ∧ (0 : Int) ≠ 0) ∨
       ((0 : Int) = 0 ∧ (0 : Int) ≠ 0)) := by
    simpa [exactlyTwoAreEqual, parseThreeNumbers] using (he hc)
  exact disj_all_equal_false (x := (0 : Int)) hP
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  findDifferentNumber input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧
  isValidIntegerString result ∧
  result = findDifferentNumber input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  exact False.elim (precond_false input h_precond)
-- </vc-theorems>
