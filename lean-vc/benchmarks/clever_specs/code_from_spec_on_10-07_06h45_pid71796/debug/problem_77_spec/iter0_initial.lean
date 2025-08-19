import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists n: Int, a = n^3
-- program termination
∃ result, implementation a = result ∧
spec result

-- LLM HELPER
def cube_root_approx (a: Int) : Int :=
  if a ≥ 0 then
    Int.natAbs (Int.sqrt (Int.natAbs a))
  else
    -(Int.natAbs (Int.sqrt (Int.natAbs a)))

-- LLM HELPER
def is_perfect_cube_helper (a: Int) (guess: Int) : Bool :=
  let candidates := [guess - 1, guess, guess + 1, guess + 2]
  candidates.any (fun n => n^3 = a)

def implementation (a: Int) : Bool := 
  if a = 0 then true
  else if a > 0 then
    let upper_bound := Int.natAbs a
    let candidates := List.range (upper_bound + 1) |>.map Int.natCast
    candidates.any (fun n => n^3 = a)
  else
    let upper_bound := Int.natAbs a
    let pos_candidates := List.range (upper_bound + 1) |>.map Int.natCast
    pos_candidates.any (fun n => (-n)^3 = a)

-- LLM HELPER
lemma cube_zero : (0 : Int)^3 = 0 := by simp

-- LLM HELPER
lemma exists_cube_zero : ∃ n: Int, (0 : Int) = n^3 := by
  use 0
  exact cube_zero.symm

-- LLM HELPER
lemma pos_cube_in_range (a: Int) (n: Int) (h1: a > 0) (h2: n^3 = a) : 
  0 ≤ n ∧ n ≤ Int.natAbs a := by
  constructor
  · by_contra h
    simp at h
    have : n^3 ≤ 0 := by
      have : n ≤ -1 := Int.le_neg_iff_add_nonpos_zero.mpr (Int.add_nonpos_of_nonpos_of_nonpos h (by norm_num))
      have : n^3 ≤ (-1)^3 := by
        apply pow_le_pow_right
        · norm_num
        · exact this
      simp at this
      exact this
    rw [←h2] at this
    linarith
  · by_contra h
    simp at h
    have : n^3 > (Int.natAbs a)^3 := by
      apply pow_lt_pow_right
      · simp [Int.natAbs_pos.mpr (ne_of_gt h1)]
      · simp [Int.natAbs_of_nonneg (le_of_lt h1)]
        exact h
    rw [←h2] at this
    simp [Int.natAbs_of_nonneg (le_of_lt h1)] at this
    linarith

-- LLM HELPER
lemma neg_cube_in_range (a: Int) (n: Int) (h1: a < 0) (h2: n^3 = a) : 
  n ≤ 0 ∧ -n ≤ Int.natAbs a := by
  constructor
  · by_contra h
    simp at h
    have : n^3 > 0 := by
      have : n ≥ 1 := h
      have : n^3 ≥ 1^3 := by
        apply pow_le_pow_right
        · norm_num
        · exact h
      simp at this
      linarith
    rw [←h2] at this
    linarith
  · by_contra h
    simp at h
    have : n^3 < (-(Int.natAbs a))^3 := by
      apply pow_lt_pow_right_of_neg
      · simp [Int.natAbs_neg, Int.natAbs_of_nonneg (le_of_lt (neg_pos.mpr h1))]
        exact neg_neg_iff_pos.mpr (Int.natAbs_pos.mpr (ne_of_lt h1))
      · simp [Int.natAbs_neg] at h
        exact neg_lt_neg h
    rw [←h2] at this
    simp [Int.natAbs_neg, neg_pow_odd] at this
    linarith

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  unfold problem_spec
  simp
  constructor
  · rfl
  · unfold implementation
    by_cases h : a = 0
    · subst h
      simp
      constructor
      · exact exists_cube_zero
      · intro ⟨n, hn⟩
        simp at hn
        exact hn.symm ▸ cube_zero
    · by_cases h1 : a > 0
      · simp [h1]
        constructor
        · intro ⟨n, hn⟩
          have bounds := pos_cube_in_range a n h1 hn
          have : Int.natCast n ∈ (List.range (Int.natAbs a + 1) |>.map Int.natCast) := by
            simp [List.mem_map, List.mem_range]
            use Int.natAbs n
            constructor
            · simp [Int.natAbs_of_nonneg bounds.1]
              linarith [bounds.2]
            · simp [Int.natCast_natAbs, abs_of_nonneg bounds.1]
          exact List.any_of_mem (fun n => n^3 = a) this hn
        · intro h_any
          simp [List.any_eq_true] at h_any
          obtain ⟨n, hn_mem, hn_cube⟩ := h_any
          exact ⟨n, hn_cube⟩
      · have h2 : a < 0 := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm (ne_of_not_not_neq h))
        simp [h1, h2]
        constructor
        · intro ⟨n, hn⟩
          have bounds := neg_cube_in_range a n h2 hn
          have : Int.natCast (-n) ∈ (List.range (Int.natAbs a + 1) |>.map Int.natCast) := by
            simp [List.mem_map, List.mem_range]
            use Int.natAbs (-n)
            constructor
            · simp [Int.natAbs_of_nonneg (neg_nonneg.mpr bounds.1)]
              linarith [bounds.2]
            · simp [Int.natCast_natAbs, abs_of_nonneg (neg_nonneg.mpr bounds.1)]
          have : (-Int.natCast (-n))^3 = a := by
            simp [neg_pow_odd]
            exact hn
          exact List.any_of_mem (fun m => (-m)^3 = a) this this
        · intro h_any
          simp [List.any_eq_true] at h_any
          obtain ⟨m, hm_mem, hm_cube⟩ := h_any
          exact ⟨-m, by simp [neg_pow_odd] at hm_cube; exact hm_cube⟩