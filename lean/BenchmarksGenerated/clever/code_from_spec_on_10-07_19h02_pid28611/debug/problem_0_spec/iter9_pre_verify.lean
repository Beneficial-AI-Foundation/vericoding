import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def specification
(impl: List Rat → Rat → Bool) (numbers: List Rat) (threshold: Rat) :=
  let numbers_within_threshold :=
    (∃ i j, i < numbers.length ∧ j < numbers.length ∧
    i ≠ j ∧ |numbers.get! i - numbers.get! j| < threshold);
  let spec (res: Bool) :=
    numbers.length > 1 → if res then numbers_within_threshold else ¬numbers_within_threshold;
    ∃ result, impl numbers threshold = result ∧ spec result

-- LLM HELPER
def has_close_pair (numbers: List Rat) (threshold: Rat) : Bool :=
  match numbers with
  | [] => false
  | [_] => false
  | x :: xs => 
    let check_against_x := xs.any (fun y => |x - y| < threshold)
    check_against_x || has_close_pair xs threshold

def implementation (numbers: List Rat) (threshold: Rat) : Bool := has_close_pair numbers threshold

-- LLM HELPER
lemma List.get!_mem (l : List Rat) (i : Nat) (hi : i < l.length) : l.get! i ∈ l := by
  have : l.get! i = l.get ⟨i, hi⟩ := by
    simp [List.get!]
    rw [List.get?_eq_get]
    simp
  rw [this]
  exact List.get_mem l ⟨i, hi⟩

-- LLM HELPER
lemma has_close_pair_correct (numbers: List Rat) (threshold: Rat) :
  has_close_pair numbers threshold = true ↔ 
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers.get! i - numbers.get! j| < threshold := by
  induction numbers with
  | nil => 
    simp [has_close_pair]
    constructor
    · intro h
      contradiction
    · intro ⟨i, j, hi, hj, _, _⟩
      simp at hi
  | cons x xs ih =>
    simp [has_close_pair]
    constructor
    · intro h
      cases h with
      | inl h_any =>
        simp [List.any_eq_true] at h_any
        obtain ⟨y, hy_mem, hy_close⟩ := h_any
        obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_get.mp hy_mem
        use 0, k + 1
        simp [List.length_cons]
        constructor
        · simp
        constructor
        · simp
          exact Nat.succ_lt_succ hk_lt
        constructor
        · simp
        · simp [List.get!]
          rw [List.get?_eq_get]
          simp
          rw [← hk_eq]
          exact hy_close
      | inr h_rec =>
        rw [ih] at h_rec
        obtain ⟨i, j, hi, hj, hij, h_close⟩ := h_rec
        use i + 1, j + 1
        simp [List.length_cons]
        constructor
        · exact Nat.succ_lt_succ hi
        constructor
        · exact Nat.succ_lt_succ hj
        constructor
        · simp [hij]
        · simp [List.get!]
          rw [List.get?_eq_get]
          simp
          exact h_close
    · intro ⟨i, j, hi, hj, hij, h_close⟩
      simp [List.length_cons] at hi hj
      cases i with
      | zero =>
        cases j with
        | zero =>
          simp at hij
        | succ j' =>
          left
          simp [List.any_eq_true]
          have hj'_lt : j' < xs.length := by
            simp at hj
            exact Nat.lt_of_succ_lt_succ hj
          use xs.get! j'
          constructor
          · exact List.get!_mem xs j' hj'_lt
          · simp [List.get!] at h_close
            rw [List.get?_eq_get] at h_close
            simp at h_close
            exact h_close
      | succ i' =>
        cases j with
        | zero =>
          left
          simp [List.any_eq_true]
          have hi'_lt : i' < xs.length := by
            simp at hi
            exact Nat.lt_of_succ_lt_succ hi
          use xs.get! i'
          constructor
          · exact List.get!_mem xs i' hi'_lt
          · simp [List.get!] at h_close
            rw [List.get?_eq_get] at h_close
            simp at h_close
            rw [abs_sub_comm]
            exact h_close
        | succ j' =>
          right
          rw [ih]
          use i', j'
          simp at hi hj hij
          simp [List.get!] at h_close
          rw [List.get?_eq_get] at h_close
          simp at h_close
          exact ⟨Nat.lt_of_succ_lt_succ hi, Nat.lt_of_succ_lt_succ hj, 
                 Nat.succ_injective.ne_iff.mp hij, h_close⟩

-- LLM HELPER
lemma has_close_pair_false (numbers: List Rat) (threshold: Rat) :
  has_close_pair numbers threshold = false ↔ 
  ¬∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers.get! i - numbers.get! j| < threshold := by
  rw [← has_close_pair_correct]
  cases h : has_close_pair numbers threshold with
  | true => simp
  | false => simp

theorem correctness (numbers: List Rat) (threshold: Rat)
: specification implementation numbers threshold := by
  simp [specification, implementation]
  use has_close_pair numbers threshold
  constructor
  · rfl
  · intro h_len
    cases h_result : has_close_pair numbers threshold with
    | true =>
      simp
      rw [has_close_pair_correct]
      exact h_result
    | false =>
      simp
      rw [has_close_pair_false]
      exact h_result