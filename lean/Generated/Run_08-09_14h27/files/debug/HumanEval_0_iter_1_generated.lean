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
-- if result then spec else ¬spec

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
        simp [List.any_eq_true] at h1
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
        · simp [List.get_cons_succ, ← hk_eq]
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
        · simp [List.get_cons_succ]
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
          simp [List.any_eq_true]
          use tail[j - 1]!
          constructor
          · apply List.get_mem
          · simp [hi_zero, List.get_cons_zero] at h_close
            cases' j with j'
            · simp at hj_pos
            · simp [List.get_cons_succ] at h_close
              exact h_close
      · cases' Nat.eq_zero_or_pos j with hj_zero hj_pos
        · left
          simp [List.any_eq_true]
          use tail[i - 1]!
          constructor
          · apply List.get_mem
          · simp [hj_zero, List.get_cons_zero] at h_close
            cases' i with i'
            · simp at hi_pos
            · simp [List.get_cons_succ] at h_close
              rw [abs_sub_comm]
              exact h_close
        · right
          apply ih
          · simp [List.length_cons] at hi_lt
            cases' i with i'
            · simp at hi_pos
            · omega
          · simp [List.length_cons] at hj_lt
            cases' j with j'
            · simp at hj_pos
            · omega
          · cases' i with i' <;> cases' j with j'
            · simp at hi_pos
            · simp at hi_pos
            · simp at hj_pos
            · simp at hi_ne_j
              omega
          · cases' i with i' <;> cases' j with j'
            · simp at hi_pos
            · simp at hi_pos
            · simp at hj_pos
            · simp [List.get_cons_succ] at h_close
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
    by_cases h : check_pairs numbers threshold
    · simp [h]
      rw [check_pairs_correct]
      exact h
    · simp [h]
      rw [← check_pairs_correct]
      exact h

-- #test implementation ([1, 2, 3]: List Rat) 0.5 = false
-- #test implementation ([1, 2.8, 3, 4, 5, 2]: List Rat) 0.3 = true