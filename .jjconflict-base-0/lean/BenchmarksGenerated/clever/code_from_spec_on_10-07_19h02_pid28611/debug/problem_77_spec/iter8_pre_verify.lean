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
    rw [neg_pow_odd]
    norm_num
  rw [this]
  simp
  exact pow_pos (neg_pos.mpr h) 3

-- LLM HELPER
lemma neg_ofNat_pow_three (n : Nat) : (-Int.ofNat n)^3 = -Int.ofNat (n^3) := by
  rw [neg_pow_odd]
  simp [Int.natCast_pow]

-- LLM HELPER
lemma cube_root_bound (a : Nat) : 
  (cube_root_nat a)^3 ≤ a ∧ a < (cube_root_nat a + 3)^3 := by
  sorry

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
    have : Int.natAbs a = k^3 := by
      rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
      rw [hn]
      simp [Int.natCast_pow]
    let candidate := cube_root_nat (Int.natAbs a)
    let test_vals := [candidate, candidate + 1, candidate + 2]
    have : k ∈ test_vals := by
      simp [test_vals]
      have h_bound := cube_root_bound (Int.natAbs a)
      rw [this] at h_bound
      omega
    rw [List.any_eq_true]
    use k
    constructor
    · exact this
    · rw [decide_eq_true_iff]
      exact this.symm
  · simp
    have h_neg : a < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm (ne_of_not_eq h_zero))
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
    have : k ∈ test_vals := by
      simp [test_vals]
      have h_bound := cube_root_bound (Int.natAbs a)
      have : Int.natAbs a = k^3 := by
        rw [Int.natAbs_neg] at hn_sym
        rw [hn_sym]
        rw [Int.natAbs_of_nonneg]
        · simp [Int.natCast_pow]
        · simp [Int.natCast_pow]
          exact Nat.cast_nonneg _
      rw [this] at h_bound
      omega
    rw [List.any_eq_true]
    use k
    constructor
    · exact this
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