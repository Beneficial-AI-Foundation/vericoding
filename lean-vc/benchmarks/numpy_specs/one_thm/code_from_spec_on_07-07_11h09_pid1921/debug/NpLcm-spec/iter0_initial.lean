namespace NpLcm

-- LLM HELPER
def gcdInt (a b : Int) : Int :=
  Int.gcd (Int.natAbs a) (Int.natAbs b)

-- LLM HELPER
lemma gcdInt_pos (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : gcdInt a b > 0 := by
  unfold gcdInt
  apply Int.coe_nat_pos.mpr
  apply Nat.gcd_pos_of_pos_left
  cases h with
  | inl ha => 
    rw [Int.natAbs_pos]
    exact ha
  | inr hb =>
    rw [Int.natAbs_pos]
    exact hb

def lcmInt (a b : Int) : Int := 
  if a = 0 ∨ b = 0 then 0 else Int.natAbs a * Int.natAbs b / gcdInt a b

-- LLM HELPER
lemma lcmInt_zero_left (b : Int) : lcmInt 0 b = 0 := by
  unfold lcmInt
  simp

-- LLM HELPER
lemma lcmInt_zero_right (a : Int) : lcmInt a 0 = 0 := by
  unfold lcmInt
  simp

-- LLM HELPER
lemma lcmInt_nonzero (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 
  lcmInt a b = Int.natAbs a * Int.natAbs b / gcdInt a b := by
  unfold lcmInt
  simp [ha, hb]

-- LLM HELPER
lemma gcdInt_dvd_left (a b : Int) : gcdInt a b ∣ Int.natAbs a := by
  unfold gcdInt
  exact Int.coe_nat_dvd.mpr (Nat.gcd_dvd_left (Int.natAbs a) (Int.natAbs b))

-- LLM HELPER
lemma gcdInt_dvd_right (a b : Int) : gcdInt a b ∣ Int.natAbs b := by
  unfold gcdInt
  exact Int.coe_nat_dvd.mpr (Nat.gcd_dvd_right (Int.natAbs a) (Int.natAbs b))

-- LLM HELPER
lemma lcmInt_dvd_helper (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 
  a ∣ lcmInt a b ∧ b ∣ lcmInt a b := by
  constructor
  · rw [lcmInt_nonzero a b ha hb]
    have h1 : gcdInt a b ∣ Int.natAbs a := gcdInt_dvd_left a b
    have h2 : gcdInt a b ≠ 0 := by
      apply ne_of_gt
      apply gcdInt_pos a b
      left
      exact ha
    obtain ⟨k, hk⟩ := h1
    rw [hk]
    rw [Int.mul_eDiv_cancel_of_emod_eq_zero]
    · use Int.natAbs b * k
      ring
    · rw [Int.mul_emod, hk, Int.mul_emod]
      simp
  · rw [lcmInt_nonzero a b ha hb]
    have h1 : gcdInt a b ∣ Int.natAbs b := gcdInt_dvd_right a b
    have h2 : gcdInt a b ≠ 0 := by
      apply ne_of_gt
      apply gcdInt_pos a b
      right
      exact hb
    obtain ⟨k, hk⟩ := h1
    rw [hk]
    rw [Int.mul_eDiv_cancel_of_emod_eq_zero]
    · use Int.natAbs a * k
      ring
    · rw [Int.mul_emod, hk, Int.mul_emod]
      simp

theorem lcmInt_spec (a b : Int) :
  lcmInt a b ≥ 0 ∧
  lcmInt a b % a = 0 ∧
  lcmInt a b % b = 0 ∧
  ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m := by
  constructor
  · -- lcmInt a b ≥ 0
    unfold lcmInt
    by_cases h : a = 0 ∨ b = 0
    · simp [h]
    · simp [h]
      apply Int.eDiv_nonneg
      · apply Int.mul_nonneg
        · exact Int.natAbs_nonneg a
        · exact Int.natAbs_nonneg b
      · apply le_of_lt
        apply gcdInt_pos a b
        exact h
  constructor
  · -- lcmInt a b % a = 0
    by_cases ha : a = 0
    · rw [ha]
      simp
    · by_cases hb : b = 0
      · rw [hb, lcmInt_zero_right]
        simp
      · have hdvd := lcmInt_dvd_helper a b ha hb
        exact Int.emod_eq_zero_of_dvd hdvd.1
  constructor
  · -- lcmInt a b % b = 0
    by_cases hb : b = 0
    · rw [hb]
      simp
    · by_cases ha : a = 0
      · rw [ha, lcmInt_zero_left]
        simp
      · have hdvd := lcmInt_dvd_helper a b ha hb
        exact Int.emod_eq_zero_of_dvd hdvd.2
  · -- ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m
    intro m hm_pos hm_a hm_b
    by_cases ha : a = 0
    · rw [ha, lcmInt_zero_left]
      exact le_of_lt hm_pos
    · by_cases hb : b = 0
      · rw [hb, lcmInt_zero_right]
        exact le_of_lt hm_pos
      · rw [lcmInt_nonzero a b ha hb]
        have h1 : Int.natAbs a ∣ m := by
          rw [Int.natAbs_dvd_iff_dvd]
          exact Int.dvd_of_emod_eq_zero hm_a
        have h2 : Int.natAbs b ∣ m := by
          rw [Int.natAbs_dvd_iff_dvd]
          exact Int.dvd_of_emod_eq_zero hm_b
        have h3 : Int.natAbs a * Int.natAbs b ≤ m * gcdInt a b := by
          apply Int.mul_le_mul_of_nonneg_right
          · sorry -- This requires more sophisticated number theory
          · apply le_of_lt
            apply gcdInt_pos a b
            left
            exact ha
        apply Int.eDiv_le_iff_le_mul_right
        · apply gcdInt_pos a b
          left
          exact ha
        · exact h3

end NpLcm