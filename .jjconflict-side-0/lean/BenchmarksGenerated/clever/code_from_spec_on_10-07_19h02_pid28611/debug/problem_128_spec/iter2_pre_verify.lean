import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Option Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Option Int) :=
  match result with
  | none => arr = []
  | some result =>
  let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum;
    let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1;
    let has_zero := 0 ∈ arr;
    (result < 0 ↔ (neg_count_odd ∧ ¬has_zero)
      ∧ result = magnitude_sum * -1) ∧
    (0 < result ↔ (¬neg_count_odd ∧ ¬has_zero)
      ∧ result = magnitude_sum) ∧
    (result = 0 ↔ has_zero)
-- program terminates
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

def implementation (arr: List Int) : Option Int := 
  if arr = [] then none
  else
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1
    let has_zero := 0 ∈ arr
    if has_zero then some 0
    else if neg_count_odd then some (magnitude_sum * -1)
    else some magnitude_sum

-- LLM HELPER
lemma magnitude_sum_nonneg (arr : List Int) : 0 ≤ (arr.map (fun x => Int.ofNat x.natAbs)).sum := by
  induction arr with
  | nil => simp
  | cons a as ih =>
    simp [List.sum_cons]
    apply add_nonneg
    · exact Int.natCast_nonneg _
    · exact ih

-- LLM HELPER
lemma magnitude_sum_pos_of_nonzero (arr : List Int) : arr ≠ [] → ¬(0 ∈ arr) → 0 < (arr.map (fun x => Int.ofNat x.natAbs)).sum := by
  intro h_nonempty h_nozero
  cases arr with
  | nil => contradiction
  | cons a as =>
    simp [List.sum_cons]
    apply add_pos_of_pos_of_nonneg
    · exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr (by
        simp at h_nozero
        exact h_nozero.1.symm))
    · exact magnitude_sum_nonneg as

-- LLM HELPER
lemma sum_eq_zero_iff_all_abs_zero (arr : List Int) : (arr.map (fun x => Int.ofNat x.natAbs)).sum = 0 ↔ ∀ x ∈ arr, Int.natAbs x = 0 := by
  induction arr with
  | nil => simp
  | cons a as ih =>
    simp [List.sum_cons]
    constructor
    · intro h
      simp at h
      have h_a : Int.natAbs a = 0 := by
        have h_nonneg_a : 0 ≤ Int.natAbs a := Nat.cast_nonneg _
        have h_nonneg_sum : 0 ≤ (as.map (fun x => Int.ofNat x.natAbs)).sum := magnitude_sum_nonneg as
        have h_sum_zero : Int.natAbs a + (as.map (fun x => Int.ofNat x.natAbs)).sum = 0 := h
        have h_both_zero : Int.natAbs a = 0 ∧ (as.map (fun x => Int.ofNat x.natAbs)).sum = 0 := by
          exact add_eq_zero_iff_of_nonneg h_nonneg_a h_nonneg_sum |>.mp h_sum_zero
        exact h_both_zero.1
      have h_sum_zero : (as.map (fun x => Int.ofNat x.natAbs)).sum = 0 := by
        have h_nonneg_a : 0 ≤ Int.natAbs a := Nat.cast_nonneg _
        have h_nonneg_sum : 0 ≤ (as.map (fun x => Int.ofNat x.natAbs)).sum := magnitude_sum_nonneg as
        have h_sum_zero : Int.natAbs a + (as.map (fun x => Int.ofNat x.natAbs)).sum = 0 := h
        have h_both_zero : Int.natAbs a = 0 ∧ (as.map (fun x => Int.ofNat x.natAbs)).sum = 0 := by
          exact add_eq_zero_iff_of_nonneg h_nonneg_a h_nonneg_sum |>.mp h_sum_zero
        exact h_both_zero.2
      constructor
      · exact h_a
      · exact ih.mp h_sum_zero
    · intro h
      simp at h
      rw [h.1, ih.mpr h.2]
      simp

-- LLM HELPER
lemma abs_zero_iff_zero (x : Int) : Int.natAbs x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact Int.natAbs_eq_zero.mp h
  · intro h
    rw [h]
    simp

-- LLM HELPER
lemma magnitude_sum_zero_iff_has_zero (arr : List Int) : arr ≠ [] → ((arr.map (fun x => Int.ofNat x.natAbs)).sum = 0 ↔ 0 ∈ arr) := by
  intro h_nonempty
  rw [sum_eq_zero_iff_all_abs_zero]
  constructor
  · intro h_all_zero
    cases arr with
    | nil => contradiction
    | cons a as =>
      have h_a_zero : Int.natAbs a = 0 := h_all_zero a (by simp)
      have h_a_eq_zero : a = 0 := (abs_zero_iff_zero a).mp h_a_zero
      simp [h_a_eq_zero]
  · intro h_zero_mem
    intro x hx
    have h_exists : ∃ y ∈ arr, y = 0 := by
      obtain ⟨y, hy_mem, hy_zero⟩ : ∃ y, y ∈ arr ∧ y = 0 := by
        exact ⟨0, h_zero_mem, rfl⟩
      exact ⟨y, hy_mem, hy_zero⟩
    by_contra h_not_zero
    have h_x_nonzero : x ≠ 0 := by
      intro h_x_zero
      rw [h_x_zero] at h_not_zero
      simp at h_not_zero
    have h_pos : 0 < (arr.map (fun x => Int.ofNat x.natAbs)).sum := by
      cases arr with
      | nil => contradiction
      | cons a as =>
        simp [List.sum_cons]
        by_cases h_case : a = 0
        · simp [h_case]
          exact magnitude_sum_nonneg as
        · apply add_pos_of_pos_of_nonneg
          · exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr h_case)
          · exact magnitude_sum_nonneg as
    exact lt_irrefl 0 h_pos

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  unfold problem_spec implementation
  simp only [exists_prop]
  split_ifs with h1 h2 h3
  · -- Case: arr = []
    use none
    constructor
    · rfl
    · simp [h1]
  · -- Case: arr ≠ [], has_zero = true
    use some 0
    constructor
    · rfl
    · simp
      let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
      let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1
      let has_zero := 0 ∈ arr
      have h_has_zero : has_zero := h2
      constructor
      · -- result < 0 ↔ (neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum * -1
        constructor
        · intro h_neg
          simp at h_neg
        · intro h_and
          cases h_and with
          | intro h_cond h_eq =>
            cases h_cond with
            | intro h_odd h_no_zero =>
              contradiction
      constructor
      · -- 0 < result ↔ (¬neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum
        constructor
        · intro h_pos
          simp at h_pos
        · intro h_and
          cases h_and with
          | intro h_cond h_eq =>
            cases h_cond with
            | intro h_not_odd h_no_zero =>
              contradiction
      · -- result = 0 ↔ has_zero
        constructor
        · intro h_zero
          exact h_has_zero
        · intro h_has_zero_2
          rfl
  · -- Case: arr ≠ [], has_zero = false, neg_count_odd = true
    use some (((arr.map (fun x => Int.ofNat x.natAbs)).sum) * -1)
    constructor
    · rfl
    · simp
      let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
      let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1
      let has_zero := 0 ∈ arr
      have h_has_zero : ¬has_zero := h2
      have h_neg_odd : neg_count_odd := h3
      constructor
      · -- result < 0 ↔ (neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum * -1
        constructor
        · intro h_neg
          constructor
          · constructor
            · exact h_neg_odd
            · exact h_has_zero
          · rfl
        · intro h_and
          cases h_and with
          | intro h_cond h_eq =>
            rw [h_eq]
            apply mul_neg_of_pos_of_neg
            · exact magnitude_sum_pos_of_nonzero arr h1 h_has_zero
            · norm_num
      constructor
      · -- 0 < result ↔ (¬neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum
        constructor
        · intro h_pos
          have h_neg : magnitude_sum * -1 < 0 := by
            apply mul_neg_of_pos_of_neg
            · exact magnitude_sum_pos_of_nonzero arr h1 h_has_zero
            · norm_num
          linarith
        · intro h_and
          cases h_and with
          | intro h_cond h_eq =>
            cases h_cond with
            | intro h_not_odd h_no_zero =>
              contradiction
      · -- result = 0 ↔ has_zero
        constructor
        · intro h_zero
          have h_neg : magnitude_sum * -1 < 0 := by
            apply mul_neg_of_pos_of_neg
            · exact magnitude_sum_pos_of_nonzero arr h1 h_has_zero
            · norm_num
          linarith
        · intro h_has_zero_2
          contradiction
  · -- Case: arr ≠ [], has_zero = false, neg_count_odd = false
    use some ((arr.map (fun x => Int.ofNat x.natAbs)).sum)
    constructor
    · rfl
    · simp
      let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
      let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1
      let has_zero := 0 ∈ arr
      have h_has_zero : ¬has_zero := h2
      have h_not_neg_odd : ¬neg_count_odd := h3
      constructor
      · -- result < 0 ↔ (neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum * -1
        constructor
        · intro h_neg
          have h_pos : 0 < magnitude_sum := by
            exact magnitude_sum_pos_of_nonzero arr h1 h_has_zero
          linarith
        · intro h_and
          cases h_and with
          | intro h_cond h_eq =>
            cases h_cond with
            | intro h_odd h_no_zero =>
              contradiction
      constructor
      · -- 0 < result ↔ (¬neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum
        constructor
        · intro h_pos
          constructor
          · constructor
            · exact h_not_neg_odd
            · exact h_has_zero
          · rfl
        · intro h_and
          cases h_and with
          | intro h_cond h_eq =>
            rw [h_eq]
            exact magnitude_sum_pos_of_nonzero arr h1 h_has_zero
      · -- result = 0 ↔ has_zero
        constructor
        · intro h_zero
          have h_pos : 0 < magnitude_sum := by
            exact magnitude_sum_pos_of_nonzero arr h1 h_has_zero
          linarith
        · intro h_has_zero_2
          contradiction