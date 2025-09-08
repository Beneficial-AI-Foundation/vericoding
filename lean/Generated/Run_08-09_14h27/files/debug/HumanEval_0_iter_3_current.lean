import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def check_pairs (numbers: List Rat) (threshold: Rat) : Bool :=
  match numbers with
  | [] => false
  | h :: t => 
    (t.any (fun x => |h - x| < threshold)) || check_pairs t threshold

def implementation (numbers: List Rat) (threshold: Rat) : Bool :=
  check_pairs numbers threshold

def problem_spec
-- function signature
(impl: List Rat → Rat → Bool)
-- inputs
(numbers: List Rat)
(threshold: Rat) :=
-- spec
let numbers_within_threshold :=
(∃ i j, i < numbers.length ∧ j < numbers.length ∧
i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold);
let spec (res: Bool) :=
numbers.length > 1 →
if res then numbers_within_threshold else ¬numbers_within_threshold;
-- program terminates
∃ result, impl numbers threshold = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma check_pairs_correct (numbers: List Rat) (threshold: Rat) :
  check_pairs numbers threshold = true ↔ 
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold := by
  constructor
  · intro h
    induction numbers with
    | nil => simp [check_pairs] at h
    | cons head tail ih =>
      simp [check_pairs] at h
      cases h with
      | inl h1 =>
        simp at h1
        obtain ⟨x, hx_mem, hx_close⟩ := h1
        obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_get.mp hx_mem
        use 0, k + 1
        simp [List.length_cons]
        constructor
        · simp
        constructor
        · omega
        constructor
        · omega
        · rw [← hk_eq] at hx_close
          simp [List.get_cons_zero, List.get_cons_succ]
          exact hx_close
      | inr h2 =>
        obtain ⟨i, j, hi_lt, hj_lt, hi_ne_j, h_close⟩ := ih h2
        use i + 1, j + 1
        simp [List.length_cons]
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        · rw [List.get_cons_succ, List.get_cons_succ]
          exact h_close
  · intro h
    obtain ⟨i, j, hi_lt, hj_lt, hi_ne_j, h_close⟩ := h
    induction numbers generalizing i j with
    | nil => simp at hi_lt
    | cons head tail ih =>
      simp [check_pairs]
      cases' Nat.eq_zero_or_pos i with hi_zero hi_pos
      · cases' Nat.eq_zero_or_pos j with hj_zero hj_pos
        · simp [hi_zero, hj_zero] at hi_ne_j
        · left
          use tail[j - 1]!
          constructor
          · have hj_pos' : j ≥ 1 := hj_pos
            have : j - 1 < tail.length := by
              simp [List.length_cons] at hj_lt
              omega
            apply List.get_mem
          · rw [hi_zero, List.get_cons_zero] at h_close
            cases' j with j'
            · simp at hj_pos
            · rw [List.get_cons_succ] at h_close
              exact h_close
      · cases' Nat.eq_zero_or_pos j with hj_zero hj_pos
        · left
          use tail[i - 1]!
          constructor
          · have hi_pos' : i ≥ 1 := hi_pos
            have : i - 1 < tail.length := by
              simp [List.length_cons] at hi_lt
              omega
            apply List.get_mem
          · rw [hj_zero, List.get_cons_zero] at h_close
            cases' i with i'
            · simp at hi_pos
            · rw [List.get_cons_succ] at h_close
              rw [abs_sub_comm]
              exact h_close
        · right
          cases' i with i'
          · simp at hi_pos
          · cases' j with j'
            · simp at hj_pos
            · apply ih
              · have : i' < tail.length := by
                  simp [List.length_cons] at hi_lt
                  omega
                exact this
              · have : j' < tail.length := by
                  simp [List.length_cons] at hj_lt
                  omega
                exact this
              · intro h_eq
                have : i' + 1 = j' + 1 := by rw [h_eq]
                have : i' = j' := Nat.succ.inj this
                rw [this] at hi_ne_j
                exact hi_ne_j rfl
              · rw [List.get_cons_succ, List.get_cons_succ] at h_close
                exact h_close

theorem correctness
(numbers: List Rat)
(threshold: Rat)
: problem_spec implementation numbers threshold  := by
  simp [problem_spec, implementation]
  use check_pairs numbers threshold
  constructor
  · rfl
  · intro h_len
    by_cases h : check_pairs numbers threshold = true
    · simp [h]
      rw [check_pairs_correct]
      exact h
    · simp [Bool.eq_false_iff_not_eq_true.mpr h]
      intro ⟨i, j, hi_lt, hj_lt, hi_ne_j, h_close⟩ 
      have : check_pairs numbers threshold = true := by
        rw [check_pairs_correct]
        exact ⟨i, j, hi_lt, hj_lt, hi_ne_j, h_close⟩
      exact h this