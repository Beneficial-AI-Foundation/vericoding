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
    (Nat.repr (result[i]!)).length < (Nat.repr (result[j]!)).length ∨
    ((Nat.repr (result[i]!)).length = (Nat.repr (result[j]!)).length ∧ result[i]! < result[j]!))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def digitCount (n : Nat) : Nat := (Nat.repr n).length

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
  simp [List.count_mergeSort]

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) (cmp : Nat → Nat → Bool) :
  lst.length = (lst.mergeSort cmp).length := by
  simp [List.length_mergeSort]

-- LLM HELPER
lemma mergeSort_sorted (lst : List Nat) (cmp : Nat → Nat → Bool) :
  let sorted := lst.mergeSort cmp
  ∀ i j : Nat, i < j → j < sorted.length → cmp (sorted[i]!) (sorted[j]!) = true := by
  intros i j hij hjlen
  apply List.mergeSort_sorted
  exact hij
  exact hjlen

-- LLM HELPER
lemma compareByDigitsAndValue_correct (a b : Nat) :
  compareByDigitsAndValue a b = true ↔ 
  (digitCount a < digitCount b ∨ (digitCount a = digitCount b ∧ a < b)) := by
  unfold compareByDigitsAndValue
  simp only [digitCount]
  by_cases h : (Nat.repr a).length < (Nat.repr b).length
  · simp [h]
    left
    exact h
  · simp [h]
    by_cases h2 : (Nat.repr a).length > (Nat.repr b).length
    · simp [h2]
      constructor
      · intro hab
        right
        constructor
        · omega
        · exact hab
      · intro hc
        cases hc with
        | inl hl => omega
        | inr hr => exact hr.2
    · simp [h2]
      constructor
      · intro hab
        right
        constructor
        · omega
        · exact hab
      · intro hc
        cases hc with
        | inl hl => omega
        | inr hr => exact hr.2

-- LLM HELPER
lemma digitCount_eq_repr_length (n : Nat) :
  digitCount n = (Nat.repr n).length := by
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
    · rw [← mergeSort_count]
    · constructor
      · rw [← mergeSort_length]
      · intros i j hij hjlen
        have h := mergeSort_sorted lst compareByDigitsAndValue i j hij hjlen
        rw [compareByDigitsAndValue_correct] at h
        cases h with
        | inl h1 => 
          left
          rw [digitCount_eq_repr_length, digitCount_eq_repr_length]
          exact h1
        | inr h2 =>
          right
          constructor
          · rw [digitCount_eq_repr_length, digitCount_eq_repr_length]
            exact h2.1
          · exact h2.2