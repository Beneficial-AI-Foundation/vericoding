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
    check 1
  else
    let rec check (n: Nat) : Bool :=
      if (Int.ofNat n)^3 = Int.natAbs a then true
      else if (Int.ofNat n)^3 > Int.natAbs a then false
      else check (n + 1)
    termination_by Int.natAbs a - (Int.ofNat n)^3
    check 1

def implementation (a: Int) : Bool := is_perfect_cube a

-- LLM HELPER
lemma cube_root_exists_iff (a: Int) : 
  (∃ n: Int, a = n^3) ↔ is_perfect_cube a = true := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    simp [is_perfect_cube]
    if h_zero : a = 0 then
      simp [h_zero]
    else if h_pos : a > 0 then
      simp [h_pos]
      have n_pos : n > 0 := by
        by_contra h_neg
        push_neg at h_neg
        cases' Nat.le_iff_lt_or_eq.mp (Int.natCast_nonneg.mp h_neg) with h h
        · have : n^3 ≤ 0 := by
            cases' Int.lt_iff_le_and_ne.mp h with h_le h_ne
            exact Int.pow_nonpos h_le (by norm_num : 0 < 3)
          rw [←hn] at this
          exact not_le.mpr h_pos this
        · rw [←h] at hn
          simp at hn
          rw [hn] at h_zero
          exact h_zero rfl
      have : ∃ k : Nat, n = Int.ofNat k ∧ k > 0 := by
        use Int.natAbs n
        constructor
        · exact Int.natCast_natAbs n
        · rw [Int.natAbs_pos]
          exact ne_of_gt n_pos
      obtain ⟨k, hk_eq, hk_pos⟩ := this
      sorry
    else
      simp [h_pos]
      have h_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm h_zero)
      have n_neg : n < 0 := by
        by_contra h_nonneg
        push_neg at h_nonneg
        have : 0 ≤ n^3 := by
          cases' Nat.le_iff_lt_or_eq.mp h_nonneg with h h
          · exact Int.pow_nonneg (le_of_lt h) 3
          · rw [←h]; simp
        rw [←hn] at this
        exact not_le.mpr h_neg this
      sorry
  · intro h
    simp [is_perfect_cube] at h
    if h_zero : a = 0 then
      use 0
      rw [h_zero]
      simp
    else if h_pos : a > 0 then
      simp [h_pos] at h
      sorry
    else
      simp [h_pos] at h
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