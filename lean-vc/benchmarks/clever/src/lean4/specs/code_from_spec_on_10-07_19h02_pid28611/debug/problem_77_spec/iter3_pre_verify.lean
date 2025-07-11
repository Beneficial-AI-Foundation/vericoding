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
        exact Nat.lt_irrefl (Int.natAbs a) (Nat.lt_of_not_le h_not)
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
        exact le_antisymm h_not (le_of_not_gt h_lt)
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
    simp [is_perfect_cube]
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
      let rec prove_check (m: Nat) : k ≥ m → is_perfect_cube.check a m = true := by
        intro h_ge
        simp [is_perfect_cube.check]
        if h_eq : m^3 = Int.natAbs a then
          simp [h_eq]
        else if h_gt : m^3 > Int.natAbs a then
          rw [this] at h_gt
          have : m^3 > k^3 := h_gt
          have : m > k := by
            by_contra h_not
            push_neg at h_not
            have : m^3 ≤ k^3 := Nat.pow_le_pow_of_le_right (by norm_num) h_not
            exact not_le.mpr this this
          exact False.elim (not_le.mpr this h_ge)
        else
          simp [h_gt]
          apply prove_check (m + 1)
          cases' Nat.eq_or_lt_of_le h_ge with h_eq h_lt
          · rw [←h_eq] at this
            rw [this] at h_eq
            exact False.elim (h_eq rfl)
          · exact Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h_lt)
      exact prove_check 1 (Nat.one_le_of_lt hk_pos)
    else
      simp [h_pos]
      have h_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm h_zero)
      have n_neg : n < 0 := by
        by_contra h_nonneg
        push_neg at h_nonneg
        have : 0 ≤ n^3 := Int.pow_nonneg h_nonneg 3
        rw [←hn] at this
        exact not_le.mpr h_neg this
      have : ∃ k : Nat, n = -Int.ofNat k ∧ k > 0 := by
        use Int.natAbs n
        constructor
        · exact Int.neg_natCast_natAbs n
        · rw [Int.natAbs_pos]
          exact ne_of_lt n_neg
      obtain ⟨k, hk_eq, hk_pos⟩ := this
      rw [hk_eq] at hn
      simp [Int.neg_pow_odd] at hn
      let rec prove_check (m: Nat) : k ≥ m → is_perfect_cube.check a m = true := by
        intro h_ge
        simp [is_perfect_cube.check]
        if h_eq : (-Int.ofNat m)^3 = a then
          simp [h_eq]
        else if h_lt : (-Int.ofNat m)^3 < a then
          rw [hn] at h_lt
          simp [Int.neg_pow_odd] at h_lt
          have : -Int.ofNat m^3 < -Int.ofNat k^3 := h_lt
          have : Int.ofNat k^3 < Int.ofNat m^3 := by
            rw [←Int.neg_lt_neg_iff]
            exact this
          have : k^3 < m^3 := by
            rw [←Int.natCast_lt (α := Int)]
            exact this
          have : k < m := by
            by_contra h_not
            push_neg at h_not
            have : m^3 ≤ k^3 := Nat.pow_le_pow_of_le_right (by norm_num) h_not
            exact not_le.mpr this this
          exact False.elim (not_le.mpr this h_ge)
        else
          simp [h_lt]
          apply prove_check (m + 1)
          cases' Nat.eq_or_lt_of_le h_ge with h_eq h_lt
          · rw [←h_eq] at hn
            rw [hn] at h_eq
            simp [Int.neg_pow_odd] at h_eq
            exact False.elim (h_eq rfl)
          · exact Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h_lt)
      exact prove_check 1 (Nat.one_le_of_lt hk_pos)
  · intro h
    simp [is_perfect_cube] at h
    if h_zero : a = 0 then
      use 0
      rw [h_zero]
      simp
    else if h_pos : a > 0 then
      simp [h_pos] at h
      have : ∃ n : Nat, n^3 = Int.natAbs a := by
        let rec find_cube (m: Nat) : m^3 ≤ Int.natAbs a → ∃ n : Nat, n^3 = Int.natAbs a := by
          intro h_le
          simp [is_perfect_cube.check] at h
          if h_eq : m^3 = Int.natAbs a then
            use m
            exact h_eq
          else if h_gt : m^3 > Int.natAbs a then
            exact False.elim (not_le.mpr h_gt h_le)
          else
            apply find_cube (m + 1)
            have : m^3 < Int.natAbs a := Nat.lt_of_le_of_ne h_le (Ne.symm h_eq)
            exact Nat.le_of_lt (Nat.lt_of_lt_of_le this (Nat.le_of_not_gt h_gt))
        exact find_cube 1 (by norm_num)
      obtain ⟨n, hn⟩ := this
      use Int.ofNat n
      rw [Int.natCast_pow]
      rw [Int.natAbs_of_nonneg (le_of_lt h_pos)] at hn
      exact hn.symm
    else
      simp [h_pos] at h
      have h_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt h_pos) (Ne.symm h_zero)
      have : ∃ n : Nat, (-Int.ofNat n)^3 = a := by
        let rec find_cube (m: Nat) : (-Int.ofNat m)^3 ≥ a → ∃ n : Nat, (-Int.ofNat n)^3 = a := by
          intro h_ge
          simp [is_perfect_cube.check] at h
          if h_eq : (-Int.ofNat m)^3 = a then
            use m
            exact h_eq
          else if h_lt : (-Int.ofNat m)^3 < a then
            exact False.elim (not_le.mpr h_lt h_ge)
          else
            apply find_cube (m + 1)
            have : (-Int.ofNat m)^3 > a := lt_of_le_of_ne h_ge (Ne.symm h_eq)
            exact le_of_lt (lt_of_lt_of_le this (le_of_not_gt h_lt))
        exact find_cube 1 (by norm_num)
      obtain ⟨n, hn⟩ := this
      use -Int.ofNat n
      exact hn

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