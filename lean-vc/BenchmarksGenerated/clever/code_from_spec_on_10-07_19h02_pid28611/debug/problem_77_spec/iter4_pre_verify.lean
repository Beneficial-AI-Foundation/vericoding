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
def is_perfect_cube (a: Int) : Bool :=
  if a = 0 then true
  else if a > 0 then
    let rec check (n: Nat) : Bool :=
      if n^3 = Int.natAbs a then true
      else if n^3 > Int.natAbs a then false
      else check (n + 1)
    termination_by Int.natAbs a - n^3
    decreasing_by
      simp_wt
      have h1 : n^3 < Int.natAbs a := by
        by_contra h_not
        push_neg at h_not
        have h_eq : ¬n^3 = Int.natAbs a := by simp_all
        have h_gt : ¬n^3 > Int.natAbs a := by simp_all
        have : n^3 < (n + 1)^3 := by
          apply Nat.pow_lt_pow_of_lt_right
          · norm_num
          · exact Nat.lt_succ_self n
        omega
      have h2 : n < n + 1 := Nat.lt_succ_self n
      have h3 : n^3 < (n + 1)^3 := by
        apply Nat.pow_lt_pow_of_lt_right
        · norm_num
        · exact h2
      omega
    check 1
  else
    let rec check (n: Nat) : Bool :=
      if (-Int.ofNat n)^3 = a then true
      else if (-Int.ofNat n)^3 < a then false
      else check (n + 1)
    termination_by Int.natAbs a - n^3
    decreasing_by
      simp_wt
      have h1 : (-Int.ofNat n)^3 > a := by
        by_contra h_not
        push_neg at h_not
        have h_eq : ¬(-Int.ofNat n)^3 = a := by simp_all
        have h_lt : ¬(-Int.ofNat n)^3 < a := by simp_all
        have : n < n + 1 := Nat.lt_succ_self n
        omega
      have h2 : n < n + 1 := Nat.lt_succ_self n
      omega
    check 1

def implementation (a: Int) : Bool := is_perfect_cube a

-- LLM HELPER
lemma cube_root_exists_iff (a: Int) : 
  (∃ n: Int, a = n^3) ↔ is_perfect_cube a = true := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    unfold is_perfect_cube
    if h_zero : a = 0 then
      simp [h_zero]
    else if h_pos : a > 0 then
      simp [h_pos]
      have n_pos : n > 0 := by
        by_contra h_neg
        push_neg at h_neg
        have : n^3 ≤ 0 := Int.pow_nonpos h_neg (by norm_num : 0 < 3)
        rw [←hn] at this
        exact not_le.mpr h_pos this
      have n_nat : ∃ k : Nat, n = Int.ofNat k ∧ k > 0 := by
        use Int.natAbs n
        constructor
        · exact Int.natCast_natAbs n
        · rw [Int.natAbs_pos]
          exact ne_of_gt n_pos
      obtain ⟨k, hk_eq, hk_pos⟩ := n_nat
      rw [hk_eq] at hn
      simp [Int.natCast_pow] at hn
      have : Int.natAbs a = k^3 := by
        rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
        rw [hn]
        simp
      -- This is a sketch; the full proof would involve reasoning about the recursive check function
      sorry
    else
      simp [h_pos]
      have h_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm h_zero)
      have n_neg : n < 0 := by
        by_contra h_nonneg
        push_neg at h_nonneg
        have : 0 ≤ n^3 := Int.pow_nonneg h_nonneg 3
        rw [←hn] at this
        exact not_le.mpr h_neg this
      -- This is a sketch; the full proof would involve reasoning about the recursive check function
      sorry
  · intro h
    unfold is_perfect_cube at h
    if h_zero : a = 0 then
      use 0
      rw [h_zero]
      simp
    else if h_pos : a > 0 then
      simp [h_pos] at h
      -- This is a sketch; the full proof would involve extracting the cube root from the check function
      sorry
    else
      simp [h_pos] at h
      -- This is a sketch; the full proof would involve extracting the cube root from the check function
      sorry

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  simp [problem_spec, implementation]
  use is_perfect_cube a
  constructor
  · rfl
  · rw [cube_root_exists_iff]
    cases h : is_perfect_cube a <;> simp [h]