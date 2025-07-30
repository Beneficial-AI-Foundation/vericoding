import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
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
def cube_root_nat (a_abs : Nat) : Nat :=
  Nat.sqrt (Nat.sqrt a_abs)

-- LLM HELPER
def is_perfect_cube (a: Int) : Bool :=
  if a = 0 then true
  else if a > 0 then
    let candidate := cube_root_nat (Int.natAbs a)
    let test_vals := [candidate, candidate + 1, candidate + 2]
    test_vals.any (fun n => decide (n^3 = Int.natAbs a))
  else
    let candidate := cube_root_nat (Int.natAbs a)
    let test_vals := [candidate, candidate + 1, candidate + 2]
    test_vals.any (fun n => decide ((-Int.ofNat n)^3 = a))

def implementation (a: Int) : Bool := is_perfect_cube a

-- LLM HELPER
lemma pow_three_pos (n : Int) (h : n > 0) : n^3 > 0 := by
  exact pow_pos h 3

-- LLM HELPER
lemma pow_three_neg (n : Int) (h : n < 0) : n^3 < 0 := by
  have : n^3 = -((-n)^3) := by
    rw [← neg_pow_odd]
  rw [this]
  simp
  exact pow_pos (neg_pos.mpr h) 3

-- LLM HELPER
lemma neg_ofNat_pow_three (n : Nat) : (-Int.ofNat n)^3 = -Int.ofNat (n^3) := by
  rw [← neg_pow_odd]
  simp [Int.natCast_pow]

-- LLM HELPER
lemma cube_root_bound (a : Nat) : 
  (cube_root_nat a)^3 ≤ a ∧ a < (cube_root_nat a + 3)^3 := by
  constructor
  · simp [cube_root_nat]
    have h1 : Nat.sqrt (Nat.sqrt a) ^ 3 ≤ a := by
      have : Nat.sqrt (Nat.sqrt a) ≤ a.sqrt := Nat.sqrt_le _
      have : a.sqrt ^ 2 ≤ a := Nat.sqrt_le _
      have : Nat.sqrt (Nat.sqrt a) ^ 2 ≤ a.sqrt ^ 2 := Nat.pow_le_pow_of_le_right (by norm_num) this
      have : (Nat.sqrt (Nat.sqrt a)) ^ 2 ≤ a := le_trans this (Nat.sqrt_le _)
      have : (Nat.sqrt (Nat.sqrt a)) ^ 3 ≤ a * (Nat.sqrt (Nat.sqrt a)) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ this
      by_cases h : Nat.sqrt (Nat.sqrt a) = 0
      · rw [h]; simp
      · have : Nat.sqrt (Nat.sqrt a) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
        have : a ≥ 1 := by
          by_contra h_contra
          push_neg at h_contra
          have : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ h_contra)
          rw [this] at h
          simp [cube_root_nat] at h
          exact h rfl
        exact Nat.le_mul_of_pos_right this
    exact h1
  · simp [cube_root_nat]
    have h1 : a < (Nat.sqrt (Nat.sqrt a) + 3)^3 := by
      have : Nat.sqrt (Nat.sqrt a) < a + 1 := by
        by_cases h : a = 0
        · simp [h]
        · have : a ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
          have : Nat.sqrt (Nat.sqrt a) ≤ Nat.sqrt a := Nat.sqrt_le _
          have : Nat.sqrt a ≤ a := Nat.sqrt_le _
          exact lt_of_le_of_lt (le_trans this this) (Nat.lt_succ_self _)
      have : (Nat.sqrt (Nat.sqrt a) + 3)^3 > (Nat.sqrt (Nat.sqrt a))^3 := by
        exact Nat.pow_lt_pow_of_lt_right (by norm_num) (by norm_num)
      have : (Nat.sqrt (Nat.sqrt a))^3 ≤ a := by
        exact (cube_root_bound a).1
      have : a < (Nat.sqrt (Nat.sqrt a) + 3)^3 := by
        by_cases h : a = 0
        · simp [h]
          norm_num
        · have : (Nat.sqrt (Nat.sqrt a) + 3)^3 ≥ 27 := by
            have : Nat.sqrt (Nat.sqrt a) + 3 ≥ 3 := by norm_num
            exact Nat.pow_le_pow_of_le_right (by norm_num) this
          exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (by norm_num)
      exact this
    exact h1

-- LLM HELPER
lemma exists_cube_root_of_perfect_cube (a : Int) (h : is_perfect_cube a = true) : ∃ n : Int, a = n^3 := by
  unfold is_perfect_cube at h
  split_ifs at h with h_zero h_pos
  · use 0
    rw [h_zero]
    simp
  · simp at h
    have : ∃ n : Nat, n^3 = Int.natAbs a := by
      let candidate := cube_root_nat (Int.natAbs a)
      let test_vals := [candidate, candidate + 1, candidate + 2]
      have h_any : test_vals.any (fun n => decide (n^3 = Int.natAbs a)) = true := h
      rw [List.any_eq_true] at h_any
      obtain ⟨n, hn_mem, hn_eq⟩ := h_any
      use n
      rw [decide_eq_true_iff] at hn_eq
      exact hn_eq
    obtain ⟨n, hn⟩ := this
    use Int.ofNat n
    have : Int.natAbs a = a := Int.natAbs_of_nonneg (le_of_lt h_pos)
    rw [←this, hn]
    simp [Int.natCast_pow]
  · simp at h
    have : ∃ n : Nat, (-Int.ofNat n)^3 = a := by
      let candidate := cube_root_nat (Int.natAbs a)
      let test_vals := [candidate, candidate + 1, candidate + 2]
      have h_any : test_vals.any (fun n => decide ((-Int.ofNat n)^3 = a)) = true := h
      rw [List.any_eq_true] at h_any
      obtain ⟨n, hn_mem, hn_eq⟩ := h_any
      use n
      rw [decide_eq_true_iff] at hn_eq
      exact hn_eq
    obtain ⟨n, hn⟩ := this
    use -Int.ofNat n
    exact hn.symm

-- LLM HELPER
lemma perfect_cube_of_exists_cube_root (a : Int) (h : ∃ n : Int, a = n^3) : is_perfect_cube a = true := by
  obtain ⟨n, hn⟩ := h
  unfold is_perfect_cube
  split_ifs with h_zero h_pos
  · simp
  · simp
    have n_pos : n > 0 := by
      by_contra h_neg
      push_neg at h_neg
      have : n^3 ≤ 0 := by
        cases' le_iff_lt_or_eq.mp h_neg with h_lt h_eq
        · exact le_of_lt (pow_three_neg n h_lt)
        · rw [h_eq]; simp
      rw [←hn] at this
      exact not_le.mpr h_pos this
    have n_nat : ∃ k : Nat, n = Int.ofNat k := by
      use Int.natAbs n
      rw [Int.natAbs_of_nonneg (le_of_lt n_pos)]
    obtain ⟨k, hk_eq⟩ := n_nat
    rw [hk_eq] at hn
    have abs_eq : Int.natAbs a = k^3 := by
      rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
      rw [hn]
      simp [Int.natCast_pow]
    let candidate := cube_root_nat (Int.natAbs a)
    let test_vals := [candidate, candidate + 1, candidate + 2]
    have k_in_range : k ∈ test_vals := by
      simp [test_vals]
      have h_bound := cube_root_bound (Int.natAbs a)
      rw [abs_eq] at h_bound
      have : cube_root_nat (k^3) ≤ k := by
        simp [cube_root_nat]
        have : Nat.sqrt (Nat.sqrt (k^3)) ≤ k := by
          have : Nat.sqrt (k^3) ≤ k^2 := by
            have : k^2 * k^2 = k^4 := by ring
            have : k^3 < k^4 := by
              cases' k with k
              · simp
              · have : k + 1 ≥ 1 := by norm_num
                exact Nat.pow_lt_pow_of_lt_right this (by norm_num)
            have : k^3 ≤ k^2 * k^2 := by
              rw [← this]
              exact le_of_lt this
            exact Nat.sqrt_le_of_le_squared this
          have : Nat.sqrt (Nat.sqrt (k^3)) ≤ Nat.sqrt (k^2) := Nat.sqrt_le_sqrt this
          have : Nat.sqrt (k^2) = k := Nat.sqrt_pow 2 k
          rw [← this]
          exact le_refl _
        exact this
      have : k < cube_root_nat (k^3) + 3 := by
        have bound := h_bound.2
        rw [abs_eq] at bound
        have : cube_root_nat (k^3) ≤ k := by
          simp [cube_root_nat]
          exact Nat.sqrt_le _
        linarith
      omega
    rw [List.any_eq_true]
    use k
    constructor
    · exact k_in_range
    · rw [decide_eq_true_iff]
      exact abs_eq
  · simp
    have h_neg : a < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm h_zero)
    have n_neg : n < 0 := by
      by_contra h_nonneg
      push_neg at h_nonneg
      have : 0 ≤ n^3 := by
        cases' le_iff_lt_or_eq.mp h_nonneg with h_pos_n h_eq
        · exact le_of_lt (pow_three_pos n h_pos_n)
        · rw [h_eq]; simp
      rw [←hn] at this
      exact not_le.mpr h_neg this
    have n_form : ∃ k : Nat, n = -Int.ofNat k ∧ k > 0 := by
      use Int.natAbs n
      constructor
      · rw [Int.natAbs_neg, Int.neg_natAbs_of_neg n_neg]
      · rw [Int.natAbs_pos]
        exact ne_of_lt n_neg
    obtain ⟨k, hk_eq, hk_pos⟩ := n_form
    rw [hk_eq] at hn
    have hn_sym : (-Int.ofNat k)^3 = a := hn
    let candidate := cube_root_nat (Int.natAbs a)
    let test_vals := [candidate, candidate + 1, candidate + 2]
    have abs_eq : Int.natAbs a = k^3 := by
      have : Int.natAbs a = Int.natAbs ((-Int.ofNat k)^3) := by
        rw [← hn_sym]
      rw [this]
      rw [Int.natAbs_pow]
      rw [Int.natAbs_neg]
      rw [Int.natAbs_of_nonneg (Int.natCast_nonneg _)]
      simp [Int.natCast_pow]
    have k_in_range : k ∈ test_vals := by
      simp [test_vals]
      have h_bound := cube_root_bound (Int.natAbs a)
      rw [abs_eq] at h_bound
      have : cube_root_nat (k^3) ≤ k := by
        simp [cube_root_nat]
        exact Nat.sqrt_le _
      have : k < cube_root_nat (k^3) + 3 := by
        have bound := h_bound.2
        rw [abs_eq] at bound
        have : cube_root_nat (k^3) ≤ k := by
          simp [cube_root_nat]
          exact Nat.sqrt_le _
        linarith
      omega
    rw [List.any_eq_true]
    use k
    constructor
    · exact k_in_range
    · rw [decide_eq_true_iff]
      exact hn_sym

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  simp [problem_spec, implementation]
  use is_perfect_cube a
  constructor
  · rfl
  · constructor
    · intro h
      exact exists_cube_root_of_perfect_cube a h
    · intro h
      exact perfect_cube_of_exists_cube_root a h