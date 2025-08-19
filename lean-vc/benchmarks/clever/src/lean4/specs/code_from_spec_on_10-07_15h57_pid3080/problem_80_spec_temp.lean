import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data.get! i = s.data.get! j)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def has_duplicate_within_distance (chars : List Char) (d : Nat) : Bool :=
  match chars with
  | [] => false
  | c :: rest =>
    if (rest.take d).contains c then true
    else has_duplicate_within_distance rest d

def implementation (s: String) : Bool := 
  s.length ≥ 3 ∧ ¬ has_duplicate_within_distance s.data 2

-- LLM HELPER
lemma has_duplicate_within_distance_iff (chars : List Char) (d : Nat) :
  has_duplicate_within_distance chars d = true ↔ 
  ∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ d ∧ chars.get! i = chars.get! j := by
  induction chars with
  | nil => 
    simp [has_duplicate_within_distance]
  | cons c rest ih =>
    simp [has_duplicate_within_distance]
    constructor
    · intro h
      cases h with
      | inl h_contains =>
        have h_mem : c ∈ rest.take d := by
          rwa [List.contains_iff_mem] at h_contains
        have h_get : ∃ k, k < (rest.take d).length ∧ (rest.take d).get! k = c := by
          exact List.mem_iff_get.mp h_mem
        obtain ⟨k, hk_lt, hk_eq⟩ := h_get
        have hk_lt_rest : k < rest.length := by
          rw [List.length_take] at hk_lt
          exact Nat.lt_of_lt_of_le hk_lt (Nat.min_le_left d rest.length)
        use 0, k + 1
        constructor
        · simp
        constructor
        · simp
          exact Nat.succ_lt_succ hk_lt_rest
        constructor
        · simp
          rw [List.length_take] at hk_lt
          exact Nat.le_trans (Nat.succ_le_succ hk_lt) (Nat.succ_le_succ (Nat.min_le_left d rest.length))
        · simp [List.get!]
          rw [← hk_eq]
          simp [List.get!, List.take]
      | inr h_rec =>
        rw [ih] at h_rec
        obtain ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i_le_d, hi_eq_hj⟩ := h_rec
        use i + 1, j + 1
        constructor
        · exact Nat.succ_lt_succ hi_lt_j
        constructor
        · exact Nat.succ_lt_succ hj_lt_len
        constructor
        · simp
          exact hj_sub_i_le_d
        · simp [List.get!]
          exact hi_eq_hj
    · intro h
      obtain ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i_le_d, hi_eq_hj⟩ := h
      cases i with
      | zero =>
        left
        rw [List.contains_iff_mem]
        have h_get : (c :: rest).get! 0 = c := by simp [List.get!]
        have h_get_j : (c :: rest).get! j = rest.get! (j - 1) := by
          cases j with
          | zero => contradiction
          | succ j' => simp [List.get!]
        rw [h_get, h_get_j] at hi_eq_hj
        have hj_pos : 0 < j := hi_lt_j
        have hj_pred_lt : j - 1 < rest.length := by
          cases j with
          | zero => contradiction
          | succ j' => 
            simp at hj_lt_len
            simp
            exact Nat.lt_of_succ_lt_succ hj_lt_len
        have hj_pred_le_d : j - 1 < d := by
          have : j ≤ d := by
            cases j with
            | zero => simp
            | succ j' =>
              simp at hj_sub_i_le_d
              exact Nat.succ_le_iff.mp hj_sub_i_le_d
          cases j with
          | zero => contradiction
          | succ j' => 
            simp
            exact Nat.lt_of_succ_le this
        have h_mem_take : rest.get! (j - 1) ∈ rest.take d := by
          rw [List.mem_iff_get]
          use j - 1
          constructor
          · rw [List.length_take]
            exact Nat.lt_min_of_lt_left hj_pred_le_d hj_pred_lt
          · simp [List.get!]
        rw [hi_eq_hj] at h_mem_take
        exact h_mem_take
      | succ i' =>
        right
        rw [ih]
        use i', j - 1
        constructor
        · cases j with
          | zero => contradiction
          | succ j' =>
            simp at hi_lt_j
            exact Nat.lt_of_succ_lt_succ hi_lt_j
        constructor
        · cases j with
          | zero => contradiction
          | succ j' =>
            simp at hj_lt_len
            simp
            exact Nat.lt_of_succ_lt_succ hj_lt_len
        constructor
        · cases j with
          | zero => contradiction
          | succ j' =>
            simp at hj_sub_i_le_d
            simp
            exact Nat.le_of_succ_le_succ hj_sub_i_le_d
        · cases j with
          | zero => contradiction
          | succ j' =>
            simp [List.get!] at hi_eq_hj
            simp [List.get!]
            exact hi_eq_hj

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  use (s.length ≥ 3 ∧ ¬ has_duplicate_within_distance s.data 2)
  constructor
  · rfl
  · simp [Bool.and_iff_left_iff_imp, Bool.not_iff]
    rw [has_duplicate_within_distance_iff]
    rfl