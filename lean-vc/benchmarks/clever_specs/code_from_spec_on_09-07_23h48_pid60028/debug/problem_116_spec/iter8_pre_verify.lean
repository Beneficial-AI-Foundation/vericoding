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

-- LLM HELPER
def insertSorted (x : Nat) (sorted : List Nat) (cmp : Nat → Nat → Bool) : List Nat :=
  match sorted with
  | [] => [x]
  | y :: ys => 
    if cmp x y then x :: y :: ys
    else y :: insertSorted x ys cmp

-- LLM HELPER
def insertionSort (lst : List Nat) (cmp : Nat → Nat → Bool) : List Nat :=
  match lst with
  | [] => []
  | x :: xs =>
    let sorted := insertionSort xs cmp
    insertSorted x sorted cmp

def implementation (lst: List Nat) : List Nat := 
  insertionSort lst compareByDigitsAndValue

-- LLM HELPER
lemma insertSorted_count (x : Nat) (sorted : List Nat) (cmp : Nat → Nat → Bool) (y : Nat) :
  (insertSorted x sorted cmp).count y = (if x = y then 1 else 0) + sorted.count y := by
  induction sorted with
  | nil => simp [insertSorted]
  | cons a as ih =>
    unfold insertSorted
    by_cases h : cmp x a
    · simp [h]
      rw [List.count_cons, List.count_cons]
      ring
    · simp [h]
      rw [List.count_cons, List.count_cons, ih]
      ring

-- LLM HELPER
lemma insertionSort_count (lst : List Nat) (cmp : Nat → Nat → Bool) (x : Nat) :
  (insertionSort lst cmp).count x = lst.count x := by
  induction lst with
  | nil => simp [insertionSort]
  | cons a as ih =>
    unfold insertionSort
    rw [insertSorted_count, ih, List.count_cons]
    ring

-- LLM HELPER
lemma insertSorted_length (x : Nat) (sorted : List Nat) (cmp : Nat → Nat → Bool) :
  (insertSorted x sorted cmp).length = 1 + sorted.length := by
  induction sorted with
  | nil => simp [insertSorted]
  | cons a as ih =>
    unfold insertSorted
    by_cases h : cmp x a
    · simp [h]
    · simp [h, ih]

-- LLM HELPER
lemma insertionSort_length (lst : List Nat) (cmp : Nat → Nat → Bool) :
  (insertionSort lst cmp).length = lst.length := by
  induction lst with
  | nil => simp [insertionSort]
  | cons a as ih =>
    unfold insertionSort
    rw [insertSorted_length, ih]
    simp

-- LLM HELPER
lemma compareByDigitsAndValue_correct (a b : Nat) :
  compareByDigitsAndValue a b = true ↔ 
  (digitCount a < digitCount b ∨ (digitCount a = digitCount b ∧ a < b)) := by
  unfold compareByDigitsAndValue digitCount
  by_cases h : (Nat.repr a).length < (Nat.repr b).length
  · simp [h]
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
  digitCount n = (Nat.repr n).length := rfl

-- LLM HELPER
lemma insertSorted_sorted (x : Nat) (sorted : List Nat) (cmp : Nat → Nat → Bool) :
  (∀ i j : Nat, i < j → j < sorted.length → cmp (sorted[i]!) (sorted[j]!) = true) →
  (∀ i j : Nat, i < j → j < (insertSorted x sorted cmp).length → 
    cmp ((insertSorted x sorted cmp)[i]!) ((insertSorted x sorted cmp)[j]!) = true) := by
  intro h_sorted
  induction sorted with
  | nil => 
    simp [insertSorted]
    intros i j hij hjlen
    omega
  | cons a as ih =>
    unfold insertSorted
    by_cases h : cmp x a
    · simp [h]
      intros i j hij hjlen
      cases i with
      | zero => 
        cases j with
        | zero => omega
        | succ j' => 
          cases j' with
          | zero => exact h
          | succ j'' => 
            have : cmp a (a :: as)[j'']! = true := by
              apply h_sorted
              · omega
              · simp at hjlen
                omega
            simp at this
            exact this
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          apply h_sorted
          · omega
          · simp at hjlen
            omega
    · simp [h]
      intros i j hij hjlen
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          by_cases h2 : j' < as.length
          · apply h_sorted
            · omega
            · exact h2
          · simp at h2
            have : j' = as.length := by omega
            rw [this]
            simp [insertSorted_length] at hjlen
            have h3 : cmp a x = false := by
              rw [← Bool.not_eq_true]
              intro h4
              have : cmp x a = true := by
                apply h_sorted
                · omega
                · omega
              rw [this] at h
              exact h
            simp at h3
            exact h3
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          simp
          apply ih
          · intros ii jj hii hjj
            apply h_sorted
            · omega
            · omega
          · omega
          · simp at hjlen
            omega

-- LLM HELPER  
lemma insertionSort_sorted (lst : List Nat) (cmp : Nat → Nat → Bool) :
  ∀ i j : Nat, i < j → j < (insertionSort lst cmp).length → 
    cmp ((insertionSort lst cmp)[i]!) ((insertionSort lst cmp)[j]!) = true := by
  induction lst with
  | nil => 
    simp [insertionSort]
    intros i j hij hjlen
    omega
  | cons a as ih =>
    unfold insertionSort
    apply insertSorted_sorted
    exact ih

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use insertionSort lst compareByDigitsAndValue
  constructor
  · rfl
  · intro x
    constructor
    · rw [← insertionSort_count]
    · constructor
      · rw [← insertionSort_length]
      · intros i j hij hjlen
        have h := insertionSort_sorted lst compareByDigitsAndValue i j hij hjlen
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