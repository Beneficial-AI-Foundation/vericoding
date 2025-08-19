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
def evenRange (start_even finish_even : Nat) : List Nat :=
  if start_even > finish_even then []
  else List.range ((finish_even - start_even) / 2 + 1) |>.map (fun i => start_even + 2 * i)

def implementation (a b: Nat) : List Nat := 
  let min_a_b := min a b
  let max_a_b := max a b
  if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
  else
    let start_even := if 2 ∣ min_a_b then min_a_b else min_a_b + 1
    let finish_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
    evenRange start_even finish_even

-- LLM HELPER
lemma evenRange_all_even (start_even finish_even : Nat) (h : start_even % 2 = 0) :
  (evenRange start_even finish_even).all (fun n => n % 2 = 0) := by
  unfold evenRange
  split_ifs with h1
  · simp [List.all_nil]
  · simp [List.all_map]
    intro i _
    simp [Nat.add_mod, h, Nat.mul_mod]

-- LLM HELPER
lemma evenRange_ascending (start_even finish_even : Nat) (h : start_even % 2 = 0) :
  ∀ i, i < (evenRange start_even finish_even).length - 1 → 
  (evenRange start_even finish_even)[i+1]! - (evenRange start_even finish_even)[i]! = 2 := by
  unfold evenRange
  split_ifs with h1
  · simp
  · intro i hi
    simp [List.getElem_map, List.getElem_range]
    ring

-- LLM HELPER
lemma evenRange_length_pos (start_even finish_even : Nat) (h1 : start_even % 2 = 0) 
  (h2 : finish_even % 2 = 0) (h3 : start_even ≤ finish_even) :
  1 < (evenRange start_even finish_even).length := by
  unfold evenRange
  simp [h3]
  have : (finish_even - start_even) / 2 + 1 ≥ 1 := by
    simp [Nat.div_add_mod]
  have : start_even < finish_even ∨ start_even = finish_even := Nat.lt_or_eq_of_le h3
  cases this with
  | inl h4 => 
    have : finish_even - start_even ≥ 2 := by
      have : ∃ k, start_even + 2 * k = finish_even ∧ k ≥ 1 := by
        use (finish_even - start_even) / 2
        constructor
        · have : start_even + finish_even - start_even = finish_even := Nat.add_sub_cancel start_even finish_even
          rw [← this]
          rw [Nat.add_sub_cancel]
          have : (finish_even - start_even) % 2 = 0 := by
            rw [← Nat.mod_add_mod, Nat.sub_mod, h2, h1]
            simp
          exact Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)
        · have : 2 ≤ finish_even - start_even := by
          have : start_even + 2 ≤ finish_even := by
            have : start_even + 1 < finish_even := h4
            omega
          omega
        exact Nat.div_pos this (by norm_num)
      omega
    omega
  | inr h4 => 
    rw [h4] at h3
    simp at h3
    omega

-- LLM HELPER
lemma evenRange_first_elem (start_even finish_even : Nat) (h1 : start_even % 2 = 0) 
  (h2 : finish_even % 2 = 0) (h3 : start_even ≤ finish_even) :
  (evenRange start_even finish_even)[0]! = start_even := by
  unfold evenRange
  simp [h3, List.getElem_map, List.getElem_range]

-- LLM HELPER
lemma evenRange_last_elem (start_even finish_even : Nat) (h1 : start_even % 2 = 0) 
  (h2 : finish_even % 2 = 0) (h3 : start_even ≤ finish_even) :
  (evenRange start_even finish_even)[(evenRange start_even finish_even).length - 1]! = finish_even := by
  unfold evenRange
  simp [h3, List.getElem_map, List.getElem_range]
  have len_pos : 0 < (finish_even - start_even) / 2 + 1 := by
    simp [Nat.div_add_mod]
  rw [Nat.add_sub_cancel]
  ring

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  use implementation a b
  constructor
  · rfl
  · unfold implementation
    let min_a_b := min a b
    let max_a_b := max a b
    split_ifs with h
    · simp [h]
    · simp [h]
      let start_even := if 2 ∣ min_a_b then min_a_b else min_a_b + 1
      let finish_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
      have start_even_even : start_even % 2 = 0 := by
        unfold start_even
        split_ifs with h1
        · exact Nat.mod_eq_zero_of_dvd h1
        · have : min_a_b % 2 = 1 := by
            have : min_a_b % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
            omega
          simp [Nat.add_mod, this]
      have finish_even_even : finish_even % 2 = 0 := by
        unfold finish_even
        split_ifs with h2
        · exact Nat.mod_eq_zero_of_dvd h2
        · have : max_a_b % 2 = 1 := by
            have : max_a_b % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
            omega
          simp [Nat.sub_mod, this]
      have start_le_finish : start_even ≤ finish_even := by
        push_neg at h
        cases h with
        | inl h => 
          have : min_a_b < max_a_b := by
            simp [min_def, max_def] at h ⊢
            omega
          unfold start_even finish_even
          split_ifs with h1 h2
          · simp [min_le_max]
          · have : max_a_b % 2 = 1 := by
              have : max_a_b % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
              omega
            have : min_a_b + 1 ≤ max_a_b := Nat.succ_le_of_lt this
            omega
          · have : min_a_b % 2 = 1 := by
              have : min_a_b % 2 < 2 := Nat.mod_lit _ (by norm_num : 0 < 2)
              omega
            simp [min_le_max]
          · have : min_a_b % 2 = 1 := by
              have : min_a_b % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
              omega
            have : max_a_b % 2 = 1 := by
              have : max_a_b % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
              omega
            have : min_a_b + 1 ≤ max_a_b := Nat.succ_le_of_lt this
            omega
        | inr h =>
          have : min_a_b % 2 = 0 := by
            push_neg at h
            exact h
          unfold start_even finish_even
          split_ifs with h1 h2
          · simp [min_le_max]
          · have : max_a_b % 2 = 1 := by
              have : max_a_b % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
              omega
            have : min_a_b ≤ max_a_b := min_le_max
            omega
          · contradiction
          · contradiction
      constructor
      · exact evenRange_all_even start_even finish_even start_even_even
      constructor
      · exact evenRange_ascending start_even finish_even start_even_even
      constructor
      · exact evenRange_length_pos start_even finish_even start_even_even finish_even_even start_le_finish
      · constructor
        · exact evenRange_first_elem start_even finish_even start_even_even finish_even_even start_le_finish
        · exact evenRange_last_elem start_even finish_even start_even_even finish_even_even start_le_finish