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
lemma cube_root_bound (a : Nat) : 
  (cube_root_nat a)^3 ≤ a ∧ a < (cube_root_nat a + 3)^3 := by
  constructor
  · simp [cube_root_nat]
    have sqrt_bound : Nat.sqrt (Nat.sqrt a) ≤ a := by
      have h1 : Nat.sqrt (Nat.sqrt a) ≤ Nat.sqrt a := Nat.sqrt_le_self _
      have h2 : Nat.sqrt a ≤ a := Nat.sqrt_le_self _
      exact le_trans h1 h2
    have cube_bound : (Nat.sqrt (Nat.sqrt a))^3 ≤ a^3 := by
      exact Nat.pow_le_pow_of_le_right (by norm_num) sqrt_bound
    have cube_le : (Nat.sqrt (Nat.sqrt a))^3 ≤ a := by
      by_cases h : a = 0
      · simp [h]
      · have a_pos : a > 0 := Nat.pos_of_ne_zero h
        have : (Nat.sqrt (Nat.sqrt a))^3 ≤ a * (Nat.sqrt (Nat.sqrt a))^2 := by
          rw [← pow_succ]
          exact Nat.mul_le_mul_right _ (le_refl _)
        have : a * (Nat.sqrt (Nat.sqrt a))^2 ≤ a * a^2 := by
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_of_le_right (by norm_num) sqrt_bound)
        have : a * a^2 = a^3 := by ring
        rw [← this]
        exact le_trans this (le_refl _)
    exact cube_le
  · simp [cube_root_nat]
    have h : a < (Nat.sqrt (Nat.sqrt a) + 3)^3 := by
      have bound : (Nat.sqrt (Nat.sqrt a) + 3)^3 > (Nat.sqrt (Nat.sqrt a))^3 := by
        exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      have : (Nat.sqrt (Nat.sqrt a))^3 ≤ a := by
        exact (cube_root_bound a).1
      have gap : (Nat.sqrt (Nat.sqrt a) + 3)^3 ≥ 27 := by
        have : Nat.sqrt (Nat.sqrt a) + 3 ≥ 3 := by norm_num
        exact Nat.pow_le_pow_of_le_right (by norm_num) this
      by_cases h : a = 0
      · simp [h]; norm_num
      · have a_pos : a > 0 := Nat.pos_of_ne_zero h
        have : (Nat.sqrt (Nat.sqrt a) + 3)^3 > a := by
          calc (Nat.sqrt (Nat.sqrt a) + 3)^3 
            ≥ 27 := gap
            _ > a := by
              by_contra h_contra
              push_neg at h_contra
              have : a ≥ 27 := h_contra
              have : Nat.sqrt (Nat.sqrt a) ≥ 2 := by
                have : Nat.sqrt a ≥ 5 := by
                  have : a ≥ 25 := by linarith
                  exact Nat.sqrt_le_iff.mp this
                have : Nat.sqrt (Nat.sqrt a) ≥ 2 := by
                  have : Nat.sqrt a ≥ 4 := by linarith
                  exact Nat.sqrt_le_iff.mp this
                exact this
              have : Nat.sqrt (Nat.sqrt a) + 3 ≥ 5 := by linarith
              have : (Nat.sqrt (Nat.sqrt a) + 3)^3 ≥ 125 := by
                exact Nat.pow_le_pow_of_le_right (by norm_num) this
              linarith
        exact this
    exact h

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
        · have : n^3 < 0 := by
            rw [← Int.neg_pos_iff] at h_lt
            have : (-n)^3 > 0 := by
              exact pow_pos h_lt 3
            have : n^3 = -((-n)^3) := by
              rw [← neg_pow_odd]
            rw [this]
            exact neg_neg_of_pos this
          exact le_of_lt this
        · rw [h_eq]; simp
      rw [←hn] at this
      exact not_le.mpr h_pos this
    have n_nat : ∃ k : Nat, n = Int.ofNat k := by
      use Int.natAbs n
      exact Int.natAbs_of_nonneg (le_of_lt n_pos)
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
      have lower : cube_root_nat (k^3) ≤ k := by
        simp [cube_root_nat]
        exact Nat.sqrt_le_self _
      have upper : k < cube_root_nat (k^3) + 3 := by
        have bound := h_bound.2
        rw [abs_eq] at bound
        linarith [lower, bound]
      omega
    rw [List.any_eq_true]
    use k
    constructor
    · exact k_in_range
    · rw [decide_eq_true_iff]
      exact abs_eq
  · simp
    have h_neg : a < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm (fun h => h_zero h.symm))
    have n_neg : n < 0 := by
      by_contra h_nonneg
      push_neg at h_nonneg
      have : 0 ≤ n^3 := by
        cases' le_iff_lt_or_eq.mp h_nonneg with h_pos_n h_eq
        · exact le_of_lt (pow_pos h_pos_n 3)
        · rw [h_eq]; simp
      rw [←hn] at this
      exact not_le.mpr h_neg this
    have n_form : ∃ k : Nat, n = -Int.ofNat k ∧ k > 0 := by
      use Int.natAbs n
      constructor
      · exact Int.neg_natAbs_of_neg n_neg
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
      have lower : cube_root_nat (k^3) ≤ k := by
        simp [cube_root_nat]
        exact Nat.sqrt_le_self _
      have upper : k < cube_root_nat (k^3) + 3 := by
        have bound := h_bound.2
        rw [abs_eq] at bound
        linarith [lower, bound]
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