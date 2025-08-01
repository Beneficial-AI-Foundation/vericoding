def problem_spec
-- function signature
(implementation: String → String → String)
-- inputs
(a b: String) :=
-- spec
let spec (result: String) :=
  a.all (fun c => c = '0' ∨ c = '1') →
  b.all (fun c => c = '0' ∨ c = '1') →
  a.length = b.length →
  result.length = a.length ∧
  result.all (fun c => c = '0' ∨ c = '1') ∧
  (∀ i, i < a.length →
  let i_pos := String.Pos.mk i;
  (a.get i_pos = b.get i_pos → result.get i_pos = '0') ∧
  (a.get i_pos ≠ b.get i_pos → result.get i_pos = '1'));
-- program termination
∃ result, implementation a b = result ∧
spec result

-- LLM HELPER
def xor_bit (c1 c2: Char) : Char :=
  if c1 = c2 then '0' else '1'

-- LLM HELPER
def xor_strings_aux (s1 s2: String) (i: Nat) (acc: String) : String :=
  if i >= s1.length then acc
  else
    let pos := String.Pos.mk i
    let c1 := s1.get pos
    let c2 := s2.get pos
    let xor_c := xor_bit c1 c2
    xor_strings_aux s1 s2 (i + 1) (acc.push xor_c)

def implementation (a b: String) : String := 
  if a.length = 0 then "" else xor_strings_aux a b 0 ""

-- LLM HELPER
lemma xor_strings_aux_length (s1 s2: String) (i: Nat) (acc: String) :
  i ≤ s1.length → (xor_strings_aux s1 s2 i acc).length = acc.length + (s1.length - i) := by
  intro h
  induction' s1.length - i using Nat.strong_induction_on with n ih generalizing i acc
  unfold xor_strings_aux
  by_cases h_ge : i >= s1.length
  · simp [h_ge]
    rw [Nat.sub_eq_zero_of_le]
    exact Nat.le_of_not_gt (fun h_lt => h_ge h_lt)
  · simp [h_ge]
    have h_lt : i < s1.length := Nat.lt_of_not_ge h_ge
    have h_sub : s1.length - (i + 1) < s1.length - i := by
      rw [Nat.sub_succ]
      exact Nat.pred_lt (Nat.sub_pos_of_lt h_lt)
    rw [ih (s1.length - (i + 1)) h_sub (i + 1) (acc.push (xor_bit (s1.get (String.Pos.mk i)) (s2.get (String.Pos.mk i)))) (Nat.le_of_lt (Nat.lt_succ_of_lt h_lt))]
    simp [String.length_push]
    ring

-- LLM HELPER
lemma xor_strings_aux_all_binary (s1 s2: String) (i: Nat) (acc: String) :
  s1.all (fun c => c = '0' ∨ c = '1') →
  s2.all (fun c => c = '0' ∨ c = '1') →
  acc.all (fun c => c = '0' ∨ c = '1') →
  i ≤ s1.length →
  (xor_strings_aux s1 s2 i acc).all (fun c => c = '0' ∨ c = '1') := by
  intro h1 h2 h_acc h_i
  induction' s1.length - i using Nat.strong_induction_on with n ih generalizing i acc
  unfold xor_strings_aux
  by_cases h_ge : i >= s1.length
  · simp [h_ge]
    exact h_acc
  · simp [h_ge]
    have h_lt : i < s1.length := Nat.lt_of_not_ge h_ge
    have h_sub : s1.length - (i + 1) < s1.length - i := by
      rw [Nat.sub_succ]
      exact Nat.pred_lt (Nat.sub_pos_of_lt h_lt)
    apply ih (s1.length - (i + 1)) h_sub (i + 1) (acc.push (xor_bit (s1.get (String.Pos.mk i)) (s2.get (String.Pos.mk i)))) h1 h2
    · simp [String.all_push]
      constructor
      · exact h_acc
      · unfold xor_bit
        by_cases h_eq : s1.get (String.Pos.mk i) = s2.get (String.Pos.mk i)
        · simp [h_eq]
          left
          rfl
        · simp [h_eq]
          right
          rfl
    · exact Nat.le_of_lt (Nat.lt_succ_of_lt h_lt)

-- LLM HELPER
lemma xor_strings_aux_get (s1 s2: String) (j: Nat) :
  s1.length = s2.length →
  j < s1.length →
  let result := xor_strings_aux s1 s2 0 ""
  j < result.length →
  result.get (String.Pos.mk j) = xor_bit (s1.get (String.Pos.mk j)) (s2.get (String.Pos.mk j)) := by
  intro h_eq h_j h_result
  have h_len : result.length = s1.length := by
    unfold result
    rw [xor_strings_aux_length s1 s2 0 "" (Nat.zero_le _)]
    simp
  generalize h_result_def : xor_strings_aux s1 s2 0 "" = result
  rw [← h_result_def]
  generalize h_i : 0 = i
  generalize h_a : "" = a
  have h_acc_eq : a.length = 0 := by rw [← h_a]; simp
  have h_i_le : i ≤ j := by rw [h_i]; exact Nat.zero_le _
  rw [← h_i, ← h_a]
  induction' j - i using Nat.strong_induction_on with k ih generalizing i a
  unfold xor_strings_aux
  by_cases h_ge : i >= s1.length
  · simp [h_ge]
    have : s1.length ≤ i := h_ge
    have : j < i := Nat.lt_of_lt_of_le h_j this
    exact absurd this (Nat.not_lt_of_le h_i_le)
  · simp [h_ge]
    have h_lt : i < s1.length := Nat.lt_of_not_ge h_ge
    by_cases h_eq_ij : i = j
    · rw [h_eq_ij]
      simp
      have h_get_at_len : (a.push (xor_bit (s1.get (String.Pos.mk j)) (s2.get (String.Pos.mk j)))).get (String.Pos.mk a.length) = xor_bit (s1.get (String.Pos.mk j)) (s2.get (String.Pos.mk j)) := by
        exact String.get_push_eq _ _
      rw [h_eq_ij] at h_i_le
      have h_acc_len : a.length = j := by
        rw [h_a] at h_acc_eq
        rw [h_i] at h_i_le
        exact Nat.eq_of_le_of_lt_succ h_i_le (Nat.lt_succ_of_le (Nat.le_of_eq h_acc_eq.symm))
      rw [h_acc_len] at h_get_at_len
      exact h_get_at_len
    · have h_i_lt_j : i < j := Nat.lt_of_le_of_ne h_i_le (Ne.symm h_eq_ij)
      have h_dec : j - (i + 1) < j - i := by
        rw [Nat.sub_succ]
        exact Nat.pred_lt (Nat.sub_pos_of_lt h_i_lt_j)
      rw [← h_eq_ij]
      exact ih (j - (i + 1)) h_dec (i + 1) (a.push (xor_bit (s1.get (String.Pos.mk i)) (s2.get (String.Pos.mk i)))) h_eq (Nat.le_of_lt (Nat.lt_succ_of_lt h_i_lt_j)) rfl h_j h_result

theorem correctness (a b: String) : problem_spec implementation a b := by
  unfold problem_spec
  use implementation a b
  constructor
  · rfl
  · intro h1 h2 h_len
    unfold implementation
    by_cases h_empty : a.length = 0
    · simp [h_empty]
      rw [← h_len] at h_empty
      constructor
      · exact h_empty.symm
      · constructor
        · simp [String.all]
        · intro i h_i
          rw [h_empty] at h_i
          exact absurd h_i (Nat.not_lt_zero i)
    · simp [h_empty]
      constructor
      · rw [xor_strings_aux_length a b 0 "" (Nat.zero_le _)]
        simp
      · constructor
        · apply xor_strings_aux_all_binary
          · exact h1
          · exact h2
          · simp [String.all]
          · exact Nat.zero_le _
        · intro i h_i
          let i_pos := String.Pos.mk i
          constructor
          · intro h_eq_chars
            have h_result_len : (xor_strings_aux a b 0 "").length = a.length := by
              rw [xor_strings_aux_length a b 0 "" (Nat.zero_le _)]
              simp
            have h_i_result : i < (xor_strings_aux a b 0 "").length := by
              rw [h_result_len]
              exact h_i
            rw [xor_strings_aux_get a b i h_len h_i h_i_result]
            unfold xor_bit
            simp [h_eq_chars]
          · intro h_neq_chars
            have h_result_len : (xor_strings_aux a b 0 "").length = a.length := by
              rw [xor_strings_aux_length a b 0 "" (Nat.zero_le _)]
              simp
            have h_i_result : i < (xor_strings_aux a b 0 "").length := by
              rw [h_result_len]
              exact h_i
            rw [xor_strings_aux_get a b i h_len h_i h_i_result]
            unfold xor_bit
            simp [h_neq_chars]