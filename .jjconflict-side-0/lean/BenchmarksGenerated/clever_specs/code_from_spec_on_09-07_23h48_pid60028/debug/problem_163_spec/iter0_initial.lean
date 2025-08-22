def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => n % 2 = 0) ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def evenRange (start finish : Nat) : List Nat :=
if start > finish then []
else if start % 2 = 0 then start :: evenRange (start + 2) finish
else evenRange (start + 1) finish

def implementation (a b: Nat) : List Nat := 
let min_a_b := min a b
let max_a_b := max a b
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
else 
  let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
  let finish := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
  evenRange start finish

-- LLM HELPER
lemma evenRange_all_even (start finish : Nat) : 
  (evenRange start finish).all (fun n => n % 2 = 0) := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    simp [evenRange]
    split_ifs with h1 h2
    · simp
    · simp [List.all_cons]
      constructor
      · exact h2
      · apply ih
        omega
    · apply ih
      omega

-- LLM HELPER
lemma evenRange_ascending (start finish : Nat) : 
  let r := evenRange start finish
  ∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2 := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    intro i hi
    simp [evenRange] at hi ⊢
    split_ifs with h1 h2
    · omega
    · cases' evenRange (start + 2) finish with
      | nil => 
        simp at hi
      | cons head tail =>
        simp [List.get_cons]
        cases i with
        | zero => 
          simp
          have : head = (start + 2) := by
            sorry -- This requires more detailed proof about evenRange structure
          rw [this]
          omega
        | succ i' =>
          simp
          apply ih
          omega
    · apply ih
      omega

-- LLM HELPER
lemma evenRange_length (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) :
  1 < (evenRange start finish).length ∨ start = finish := by
  sorry

-- LLM HELPER  
lemma evenRange_first_last (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) (h_finish_even : finish % 2 = 0) :
  let r := evenRange start finish
  r.length > 0 → r[0]! = start ∧ r[r.length-1]! = finish := by
  sorry

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  use implementation a b
  constructor
  · rfl
  · simp [problem_spec]
    let min_a_b := min a b
    let max_a_b := max a b
    simp [implementation]
    split_ifs with h
    · simp
      exact h
    · constructor
      · apply evenRange_all_even
      · constructor
        · apply evenRange_ascending
        · constructor
          · sorry -- Need to prove length > 1
          · simp [h]
            sorry -- Need to prove first and last element properties