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
    · have h_a_nonzero : a ≠ 0 := by
        intro h_a_zero
        rw [h_a_zero] at h_nozero
        simp at h_nozero
      exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr h_a_nonzero)
    · exact magnitude_sum_nonneg as

-- LLM HELPER
lemma abs_eq_abs (x : Int) : Int.natAbs x = Int.natAbs (|x|) := by
  simp [Int.natAbs_of_nonneg (abs_nonneg x)]

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