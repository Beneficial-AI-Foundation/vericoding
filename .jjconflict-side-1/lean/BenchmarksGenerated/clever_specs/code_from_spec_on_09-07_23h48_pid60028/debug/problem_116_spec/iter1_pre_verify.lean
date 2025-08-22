def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  ∀ x : Nat, lst.count x = result.count x ∧
  result.length = lst.length ∧
  (∀ i j : Nat, i < j → j < result.length →
    Nat.digits 2 (result.get! i) < Nat.digits 2 (result.get! j) ∨
    (Nat.digits 2 (result.get! i) = Nat.digits 2 (result.get! j) ∧ result.get! i < result.get! j))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def digitCount (n : Nat) : Nat := (Nat.digits 2 n).length

-- LLM HELPER
def compareByDigitsAndValue (a b : Nat) : Bool :=
  let digitsA := digitCount a
  let digitsB := digitCount b
  if digitsA < digitsB then true
  else if digitsA > digitsB then false
  else a < b

def implementation (lst: List Nat) : List Nat := 
  lst.mergeSort compareByDigitsAndValue

-- LLM HELPER
lemma mergeSort_count (lst : List Nat) (cmp : Nat → Nat → Bool) (x : Nat) :
  lst.count x = (lst.mergeSort cmp).count x := by
  sorry

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) (cmp : Nat → Nat → Bool) :
  lst.length = (lst.mergeSort cmp).length := by
  sorry

-- LLM HELPER
lemma mergeSort_sorted (lst : List Nat) (cmp : Nat → Nat → Bool) :
  let sorted := lst.mergeSort cmp
  ∀ i j : Nat, i < j → j < sorted.length → cmp (sorted.get! i) (sorted.get! j) = true := by
  sorry

-- LLM HELPER
lemma compareByDigitsAndValue_correct (a b : Nat) :
  compareByDigitsAndValue a b = true ↔ 
  (digitCount a < digitCount b ∨ (digitCount a = digitCount b ∧ a < b)) := by
  sorry

-- LLM HELPER
lemma digitCount_eq_digits_length (n : Nat) :
  digitCount n = (Nat.digits 2 n).length := by
  rfl

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use lst.mergeSort compareByDigitsAndValue
  constructor
  · rfl
  · intro x
    constructor
    · rw [mergeSort_count]
    · constructor
      · rw [mergeSort_length]
      · intros i j hij hjlen
        have h := mergeSort_sorted lst compareByDigitsAndValue i j hij hjlen
        rw [compareByDigitsAndValue_correct] at h
        cases h with
        | inl h1 => 
          left
          rw [digitCount_eq_digits_length, digitCount_eq_digits_length]
          exact h1
        | inr h2 =>
          right
          constructor
          · rw [digitCount_eq_digits_length, digitCount_eq_digits_length]
            exact h2.1
          · exact h2.2