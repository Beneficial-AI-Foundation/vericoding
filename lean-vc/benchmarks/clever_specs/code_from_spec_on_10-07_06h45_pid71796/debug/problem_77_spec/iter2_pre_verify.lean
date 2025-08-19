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
def isCubeRoot (n a : Int) : Bool := n^3 = a

-- LLM HELPER
def searchCubeRoot (a : Int) (bound : Nat) : Bool :=
  if bound = 0 then false
  else
    let n := Int.ofNat bound
    if n^3 = a then true
    else if (-n)^3 = a then true
    else searchCubeRoot a (bound - 1)

def implementation (a: Int) : Bool := 
  if a = 0 then true
  else 
    let bound := Int.natAbs a
    searchCubeRoot a bound.toNat

-- LLM HELPER
lemma cube_zero : (0 : Int)^3 = 0 := by simp

-- LLM HELPER
lemma exists_cube_zero : ∃ n: Int, (0 : Int) = n^3 := by
  use 0
  exact cube_zero.symm

-- LLM HELPER
lemma searchCubeRoot_correct (a : Int) (bound : Nat) :
  searchCubeRoot a bound = true ↔ ∃ n : Int, n^3 = a ∧ Int.natAbs n ≤ bound := by
  induction bound with
  | zero => 
    simp [searchCubeRoot]
    constructor
    · intro h
      cases h
    · intro ⟨n, hn_cube, hn_bound⟩
      simp at hn_bound
      have : n = 0 := by
        have : Int.natAbs n = 0 := Nat.eq_zero_of_le_zero hn_bound
        exact Int.eq_zero_of_natAbs_eq_zero this
      subst this
      simp at hn_cube
      exact hn_cube
  | succ k ih =>
    simp [searchCubeRoot]
    constructor
    · intro h
      by_cases h1 : (Int.ofNat (k + 1))^3 = a
      · use Int.ofNat (k + 1)
        constructor
        · exact h1
        · simp [Int.natAbs_of_nonneg (Int.ofNat_nonneg _)]
      · by_cases h2 : (-(Int.ofNat (k + 1)))^3 = a
        · use -(Int.ofNat (k + 1))
          constructor
          · exact h2
          · simp [Int.natAbs_neg, Int.natAbs_of_nonneg (Int.ofNat_nonneg _)]
        · simp [h1, h2] at h
          rw [ih] at h
          obtain ⟨n, hn_cube, hn_bound⟩ := h
          use n
          constructor
          · exact hn_cube
          · exact Nat.le_succ_of_le hn_bound
    · intro ⟨n, hn_cube, hn_bound⟩
      by_cases h1 : (Int.ofNat (k + 1))^3 = a
      · simp [h1]
      · by_cases h2 : (-(Int.ofNat (k + 1)))^3 = a
        · simp [h1, h2]
        · simp [h1, h2]
          rw [ih]
          cases' Nat.eq_or_lt_of_le hn_bound with h h
          · have : Int.natAbs n = k + 1 := h
            by_cases hn_pos : n ≥ 0
            · have : n = Int.ofNat (k + 1) := by
                simp [Int.natAbs_of_nonneg hn_pos] at this
                exact Int.natCast_injective.mp this
              subst this
              exact absurd hn_cube h1
            · have : n = -(Int.ofNat (k + 1)) := by
                simp [Int.natAbs_neg, Int.natAbs_of_nonneg (Int.ofNat_nonneg _)] at this
                push_neg at hn_pos
                have : n < 0 := hn_pos
                rw [← Int.natAbs_neg] at this
                simp [Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt this))] at this
                exact Int.neg_inj.mp (Int.natCast_injective.mp this)
              subst this
              exact absurd hn_cube h2
          · use n
            exact ⟨hn_cube, Nat.le_of_succ_le_succ h⟩

-- LLM HELPER
lemma bound_sufficient (a : Int) (n : Int) (h : n^3 = a) : 
  Int.natAbs n ≤ Int.natAbs a := by
  by_cases ha : a = 0
  · subst ha
    simp at h
    have : n = 0 := by
      by_contra hn
      have : n^3 ≠ 0 := by
        cases' lt_or_gt_of_ne hn with h1 h2
        · have : n^3 < 0 := by
            have : n ≤ -1 := Int.le_neg_iff_add_nonpos_zero.mpr (Int.add_nonpos_of_nonpos_of_nonpos (le_of_lt h1) (by norm_num))
            calc n^3 
              = n * n^2 := by ring
              _ ≤ (-1) * n^2 := by apply Int.mul_le_mul_of_nonneg_right this (sq_nonneg _)
              _ = -n^2 := by ring
              _ ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
        · have : n^3 > 0 := by
            have : n ≥ 1 := h2
            have : n^3 ≥ 1 := by
              calc n^3 
                = n * n^2 := by ring
                _ ≥ 1 * n^2 := by apply Int.mul_le_mul_of_nonneg_right this (sq_nonneg _)
                _ = n^2 := by ring
                _ ≥ 1 := by
                  have : n^2 ≥ 1^2 := sq_le_sq' (by linarith) this
                  simp at this
                  exact this
            linarith
        exact this h
      exact this
    subst this
    simp
  · by_cases ha_pos : a > 0
    · have hn_pos : n > 0 := by
        by_contra h_neg
        push_neg at h_neg
        have : n^3 ≤ 0 := by
          cases' lt_or_eq_of_le h_neg with h1 h2
          · have : n^3 < 0 := by
              have : n ≤ -1 := Int.le_neg_iff_add_nonpos_zero.mpr (Int.add_nonpos_of_nonpos_of_nonpos (le_of_lt h1) (by norm_num))
              calc n^3 
                = n * n^2 := by ring
                _ ≤ (-1) * n^2 := by apply Int.mul_le_mul_of_nonneg_right this (sq_nonneg _)
                _ = -n^2 := by ring
                _ ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
          · subst h2
            simp
        rw [← h] at this
        linarith
      simp [Int.natAbs_of_nonneg (le_of_lt hn_pos), Int.natAbs_of_nonneg (le_of_lt ha_pos)]
      by_contra h_bound
      push_neg at h_bound
      have : n^3 > a^3 := by
        apply pow_lt_pow_right (by linarith) h_bound
      rw [← h] at this
      exact lt_irrefl a this
    · have ha_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt ha_pos) (Ne.symm (ne_of_eq ha))
      have hn_neg : n < 0 := by
        by_contra h_pos
        push_neg at h_pos
        have : n^3 ≥ 0 := by
          cases' lt_or_eq_of_le h_pos with h1 h2
          · have : n^3 > 0 := by
              have : n ≥ 1 := h1
              have : n^3 ≥ 1 := by
                calc n^3 
                  = n * n^2 := by ring
                  _ ≥ 1 * n^2 := by apply Int.mul_le_mul_of_nonneg_right this (sq_nonneg _)
                  _ = n^2 := by ring
                  _ ≥ 1 := by
                    have : n^2 ≥ 1^2 := sq_le_sq' (by linarith) this
                    simp at this
                    exact this
              linarith
          · subst h2
            simp
        rw [← h] at this
        linarith
      simp [Int.natAbs_neg, Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hn_neg)), 
            Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt ha_neg))]
      by_contra h_bound
      push_neg at h_bound
      have : n^3 < a^3 := by
        apply pow_lt_pow_right_of_neg (by linarith) h_bound
      rw [← h] at this
      exact lt_irrefl a this

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
    · simp [h]
      rw [searchCubeRoot_correct]
      constructor
      · intro ⟨n, hn_cube, hn_bound⟩
        use n
        exact hn_cube
      · intro ⟨n, hn_cube⟩
        use n
        constructor
        · exact hn_cube
        · exact bound_sufficient a n hn_cube