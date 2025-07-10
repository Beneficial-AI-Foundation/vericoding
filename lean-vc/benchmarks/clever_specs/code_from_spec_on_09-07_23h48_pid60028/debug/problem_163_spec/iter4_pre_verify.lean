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
termination_by finish - start
decreasing_by
  simp_wf
  split_ifs with h1 h2
  · omega
  · omega
  · omega

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
          have h_first : head = (evenRange (start + 2) finish)[0]! := by
            simp [List.get_cons]
          have h_start_even : (start + 2) % 2 = 0 := by omega
          have h_le : start + 2 ≤ finish := by omega
          have h_head_val : head = start + 2 := by
            simp [evenRange] at h_first
            split_ifs at h_first with h_gt h_even
            · omega
            · simp at h_first
              exact h_first
            · omega
          rw [h_head_val]
          omega
        | succ i' =>
          simp
          apply ih
          omega
    · apply ih
      omega

-- LLM HELPER
lemma evenRange_nonempty (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) :
  (evenRange start finish).length > 0 := by
  simp [evenRange]
  split_ifs with h1 h2
  · omega
  · simp
  · omega

-- LLM HELPER
lemma evenRange_first (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) :
  let r := evenRange start finish
  r.length > 0 → r[0]! = start := by
  simp [evenRange]
  split_ifs with h1 h2
  · omega
  · simp
  · omega

-- LLM HELPER
lemma evenRange_last (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) (h_finish_even : finish % 2 = 0) :
  let r := evenRange start finish
  r.length > 0 → r[r.length-1]! = finish := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    simp [evenRange]
    split_ifs with h1 h2
    · omega
    · intro hlen
      cases' evenRange (start + 2) finish with
      | nil => 
        simp at hlen ⊢
      | cons head tail =>
        simp
        have : (start + 2) % 2 = 0 := by omega
        have : start + 2 ≤ finish := by omega
        apply ih
        · omega
        · exact this
        · exact h_finish_even
        · simp
    · omega

-- LLM HELPER
lemma evenRange_length_ge_two (start finish : Nat) (h : start ≤ finish) (h_even : start % 2 = 0) (h_gap : start + 2 ≤ finish) :
  (evenRange start finish).length ≥ 2 := by
  simp [evenRange]
  split_ifs with h1 h2
  · omega
  · simp
    have : (evenRange (start + 2) finish).length > 0 := by
      apply evenRange_nonempty
      · omega
      · omega
    omega
  · omega

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
    · have start_le_finish : min_a_b ≤ max_a_b := by simp [min_le_max]
      let start := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
      let finish := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
      have start_even : start % 2 = 0 := by
        simp [start]
        split_ifs with h_div
        · exact Nat.mod_two_eq_zero_of_two_dvd h_div
        · simp [Nat.add_mod]
          omega
      have finish_even : finish % 2 = 0 := by
        simp [finish]
        split_ifs with h_div
        · exact Nat.mod_two_eq_zero_of_two_dvd h_div
        · have : max_a_b % 2 = 1 := by
            have : ¬(max_a_b % 2 = 0) := by
              intro h_zero
              have : 2 ∣ max_a_b := by
                rw [Nat.dvd_iff_mod_eq_zero]
                exact h_zero
              exact h_div this
            omega
          rw [Nat.sub_mod]
          simp [this]
      have start_le_finish' : start ≤ finish := by
        simp [start, finish]
        split_ifs with h1 h2
        · omega
        · omega
        · omega
        · omega
      have len_pos : (evenRange start finish).length > 0 := by
        apply evenRange_nonempty
        · exact start_le_finish'
        · exact start_even
      have len_ge_two : (evenRange start finish).length ≥ 2 := by
        apply evenRange_length_ge_two
        · exact start_le_finish'
        · exact start_even
        · simp [start, finish]
          split_ifs with h1 h2
          · omega
          · omega
          · omega
          · omega
      constructor
      · apply evenRange_all_even
      · constructor
        · apply evenRange_ascending
        · constructor
          · omega
          · simp [h]
            constructor
            · apply evenRange_first
              · exact start_le_finish'
              · exact start_even
              · exact len_pos
            · apply evenRange_last
              · exact start_le_finish'
              · exact start_even
              · exact finish_even
              · exact len_pos