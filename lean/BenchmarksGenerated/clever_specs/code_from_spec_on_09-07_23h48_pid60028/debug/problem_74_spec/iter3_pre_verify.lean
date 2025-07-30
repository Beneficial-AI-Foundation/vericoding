def problem_spec
(implementation: List String → List String → List String)
(lst1: List String) (lst2: List String) :=
let sum_chars (xs: List String) : Int :=
  xs.foldl (λ acc a => acc + a.length) 0;
let spec (result : List String) :=
  ((result = lst1) ∨ (result = lst2))
  ∧
  (sum_chars result ≤ sum_chars lst1)
  ∧
  (sum_chars result ≤ sum_chars lst2)
  ∧
  ((sum_chars lst1 = sum_chars lst2) → (result = lst1));
∃ result, implementation lst1 lst2 = result ∧
spec result

def implementation (lst1: List String) (lst2: List String) : List String :=
  let sum_chars (xs: List String) : Int :=
    List.foldl (λ acc a => acc + a.length) 0 xs
  if sum_chars lst1 ≤ sum_chars lst2 then lst1 else lst2

-- LLM HELPER
lemma le_total (a b : Int) : a ≤ b ∨ b ≤ a := Int.le_total a b

theorem correctness
(lst1: List String) (lst2: List String)
: problem_spec implementation lst1 lst2 := by
  unfold problem_spec implementation
  let sum_chars := fun xs => List.foldl (fun acc a => acc + a.length) 0 xs
  use if sum_chars lst1 ≤ sum_chars lst2 then lst1 else lst2
  constructor
  · rfl
  · constructor
    · by_cases h : sum_chars lst1 ≤ sum_chars lst2
      · simp [h]
        left
        rfl
      · simp [h]
        right
        rfl
    · constructor
      · by_cases h : sum_chars lst1 ≤ sum_chars lst2
        · simp [h]
        · simp [h]
          have : sum_chars lst2 ≤ sum_chars lst1 := by
            have : sum_chars lst1 ≤ sum_chars lst2 ∨ sum_chars lst2 ≤ sum_chars lst1 := le_total _ _
            cases this with
            | inl h' => contradiction
            | inr h' => exact h'
          exact this
      · by_cases h : sum_chars lst1 ≤ sum_chars lst2
        · simp [h]
          intro h_eq
          rfl
        · simp [h]
          intro h_eq
          have : sum_chars lst2 ≤ sum_chars lst1 := by
            have : sum_chars lst1 ≤ sum_chars lst2 ∨ sum_chars lst2 ≤ sum_chars lst1 := le_total _ _
            cases this with
            | inl h' => contradiction
            | inr h' => exact h'
          have : sum_chars lst1 ≤ sum_chars lst2 := by rw [←h_eq]; exact this
          contradiction