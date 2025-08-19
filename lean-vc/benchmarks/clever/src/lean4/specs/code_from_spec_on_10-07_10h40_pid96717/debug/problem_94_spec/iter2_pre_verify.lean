import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => decide (Nat.Prime num)) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Nat.Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Nat.Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def find_min_prime_index (lst: List Nat) : Option Nat :=
  let prime_indices := (List.range lst.length).filter (fun i => decide (Nat.Prime (lst.get! i)))
  if prime_indices.isEmpty then none
  else 
    let min_prime := prime_indices.foldl (fun acc i => 
      if lst.get! i < lst.get! acc then i else acc) prime_indices.head!
    some min_prime

def implementation (lst: List Nat) : Nat := 
  match find_min_prime_index lst with
  | none => 0
  | some i => (Nat.digits 10 (lst.get! i)).sum

-- LLM HELPER
lemma list_any_iff_exists (lst: List Nat) (p: Nat → Bool) :
  lst.any p = true ↔ ∃ i, i < lst.length ∧ p (lst.get! i) = true := by
  constructor
  · intro h
    induction lst with
    | nil => simp at h
    | cons head tail ih =>
      simp [List.any] at h
      cases' h with h h
      · use 0
        simp [h]
      · obtain ⟨i, hi_lt, hi_prop⟩ := ih h
        use i + 1
        simp [hi_lt, hi_prop]
  · intro ⟨i, hi_lt, hi_prop⟩
    induction lst with
    | nil => simp at hi_lt
    | cons head tail ih =>
      simp [List.any]
      cases' i with i
      · simp [hi_prop]
      · right
        apply ih
        use i
        simp at hi_lt hi_prop
        exact ⟨hi_lt, hi_prop⟩

-- LLM HELPER
lemma find_min_prime_index_correct (lst: List Nat) :
  (∃ i, i < lst.length ∧ Nat.Prime (lst.get! i)) →
  ∃ i, find_min_prime_index lst = some i ∧ 
       i < lst.length ∧ 
       Nat.Prime (lst.get! i) ∧
       (∀ j, j < lst.length ∧ Nat.Prime (lst.get! j) → lst.get! i ≤ lst.get! j) := by
  intro h
  obtain ⟨k, hk_lt, hk_prime⟩ := h
  unfold find_min_prime_index
  let prime_indices := (List.range lst.length).filter (fun i => decide (Nat.Prime (lst.get! i)))
  have h_nonempty : ¬prime_indices.isEmpty := by
    simp [prime_indices]
    use k
    constructor
    · exact hk_lt
    · simp [decide_eq_true_iff]
      exact hk_prime
  simp [h_nonempty]
  let min_prime := prime_indices.foldl (fun acc i => 
    if lst.get! i < lst.get! acc then i else acc) prime_indices.head!
  use min_prime
  constructor
  · rfl
  · constructor
    · have h_mem : min_prime ∈ prime_indices := by
        simp [min_prime]
        have h_head_mem : prime_indices.head! ∈ prime_indices := by
          apply List.head!_mem
          exact h_nonempty
        induction prime_indices with
        | nil => simp at h_nonempty
        | cons head tail ih =>
          simp [List.foldl]
          exact List.foldl_mem (fun acc i => if lst.get! i < lst.get! acc then i else acc) 
                               head tail (by simp)
      simp [prime_indices] at h_mem
      exact h_mem.1
    · constructor
      · have h_mem : min_prime ∈ prime_indices := by
          simp [min_prime]
          have h_head_mem : prime_indices.head! ∈ prime_indices := by
            apply List.head!_mem
            exact h_nonempty
          induction prime_indices with
          | nil => simp at h_nonempty
          | cons head tail ih =>
            simp [List.foldl]
            exact List.foldl_mem (fun acc i => if lst.get! i < lst.get! acc then i else acc) 
                                 head tail (by simp)
        simp [prime_indices] at h_mem
        simp [decide_eq_true_iff] at h_mem
        exact h_mem.2
      · intro j hj_lt hj_prime
        simp [min_prime]
        have h_j_mem : j ∈ prime_indices := by
          simp [prime_indices]
          constructor
          · exact hj_lt
          · simp [decide_eq_true_iff]
            exact hj_prime
        induction prime_indices with
        | nil => simp at h_j_mem
        | cons head tail ih =>
          simp [List.foldl]
          have h_prop : ∀ acc, acc ∈ (head :: tail) → 
            (tail.foldl (fun acc i => if lst.get! i < lst.get! acc then i else acc) acc) ∈ (head :: tail) ∧
            lst.get! (tail.foldl (fun acc i => if lst.get! i < lst.get! acc then i else acc) acc) ≤ lst.get! acc := by
            intro acc h_acc_mem
            induction tail with
            | nil => simp
            | cons t_head t_tail t_ih =>
              simp [List.foldl]
              by_cases h : lst.get! t_head < lst.get! acc
              · simp [h]
                have h_t_head_mem : t_head ∈ (head :: t_head :: t_tail) := by simp
                exact t_ih t_head h_t_head_mem
              · simp [h]
                have h_not_lt : lst.get! acc ≤ lst.get! t_head := by
                  simp at h
                  exact Nat.le_of_not_gt h
                exact t_ih acc h_acc_mem
          apply (h_prop head (by simp)).2

-- LLM HELPER
lemma digits_sum_pos (n : Nat) (hn : n > 0) : (Nat.digits 10 n).sum > 0 := by
  have h : (Nat.digits 10 n).length > 0 := by
    rw [Nat.digits_len]
    · simp [Nat.log_pos]
      exact hn
    · norm_num
  have h_nonempty : (Nat.digits 10 n) ≠ [] := by
    intro h_eq
    simp [h_eq] at h
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil h_nonempty
  have h_digit : d < 10 := by
    exact Nat.digits_lt_base (by norm_num) hd
  have h_digit_pos : d ≥ 0 := Nat.zero_le d
  rw [List.sum_pos_iff_exists_pos]
  use d
  constructor
  · exact hd
  · cases' d with d
    · simp
      have h_last : (Nat.digits 10 n).getLast h_nonempty = n % 10 := by
        rw [Nat.digits_last]
        · exact hn
        · norm_num
      have h_n_mod : n % 10 > 0 := by
        by_contra h_not
        simp at h_not
        have h_div : 10 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr h_not
        have h_ge_10 : n ≥ 10 := by
          cases' h_div with k hk
          rw [hk] at hn
          have h_k_pos : k > 0 := by
            by_contra h_k_zero
            simp at h_k_zero
            rw [hk, h_k_zero, mul_zero] at hn
            exact Nat.lt_irrefl 0 hn
          rw [hk]
          exact Nat.mul_pos (by norm_num) h_k_pos
        have h_digits_len : (Nat.digits 10 n).length > 1 := by
          rw [Nat.digits_len]
          · simp [Nat.log_pos]
            exact Nat.log_pos (by norm_num) h_ge_10
          · norm_num
        have h_not_single : ¬(Nat.digits 10 n).length = 1 := by
          exact Nat.not_eq_of_lt h_digits_len
        have h_single : (Nat.digits 10 n).length = 1 := by
          have h_eq : Nat.digits 10 n = [n % 10] := by
            cases' n with n
            · simp at hn
            · simp [Nat.digits]
              sorry
          rw [h_eq]
          simp
        exact h_not_single h_single
      rw [← Nat.digits_last (by norm_num) hn] at h_n_mod
      rw [← h_last] at h_n_mod
      have h_d_last : d = (Nat.digits 10 n).getLast h_nonempty := by
        sorry
      rw [h_d_last]
      exact h_n_mod
    · simp
      exact Nat.succ_pos d

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h
    unfold implementation
    have h_exists : ∃ i, i < lst.length ∧ Nat.Prime (lst.get! i) := by
      rw [← list_any_iff_exists] at h
      simp at h
      have h_decide : ∃ i, i < lst.length ∧ decide (Nat.Prime (lst.get! i)) = true := h
      obtain ⟨i, hi_lt, hi_decide⟩ := h_decide
      use i
      constructor
      · exact hi_lt
      · rwa [decide_eq_true_iff] at hi_decide
    obtain ⟨i, hi_some, hi_lt, hi_prime, hi_min⟩ := find_min_prime_index_correct lst h_exists
    simp [hi_some]
    constructor
    · apply digits_sum_pos
      cases' hi_prime with h1 h2
      exact h1
    · use i
      exact ⟨hi_lt, hi_prime, hi_min, rfl⟩