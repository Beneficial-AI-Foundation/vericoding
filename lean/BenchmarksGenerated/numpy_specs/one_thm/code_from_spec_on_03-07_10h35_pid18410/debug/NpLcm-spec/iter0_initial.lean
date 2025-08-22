namespace NpLcm

/- LLM HELPER -/
def gcdInt (a b : Int) : Int :=
  Int.gcd (Int.natAbs a) (Int.natAbs b)

/- LLM HELPER -/
lemma gcd_pos (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : gcdInt a b > 0 := by
  unfold gcdInt
  simp [Int.gcd_pos_iff]
  cases h with
  | inl ha => 
    left
    rw [Int.natAbs_pos]
    exact ha
  | inr hb => 
    right
    rw [Int.natAbs_pos]
    exact hb

def lcmInt (a b : Int) : Int := 
  if a = 0 ∧ b = 0 then 0
  else Int.natAbs (a * b) / gcdInt a b

/- LLM HELPER -/
lemma lcm_nonneg (a b : Int) : lcmInt a b ≥ 0 := by
  unfold lcmInt
  split_ifs
  · norm_num
  · apply Int.div_nonneg
    · exact Int.natAbs_nonneg _
    · unfold gcdInt
      exact Int.natAbs_nonneg _

/- LLM HELPER -/
lemma dvd_lcm_left (a b : Int) : a ∣ lcmInt a b := by
  unfold lcmInt
  split_ifs with h
  · cases h with
    | mk ha hb =>
      rw [ha]
      exact dvd_zero _
  · have h_not_both_zero : a ≠ 0 ∨ b ≠ 0 := by
      push_neg at h
      exact h
    unfold gcdInt
    rw [Int.dvd_iff_natAbs_dvd_natAbs]
    have : Int.natAbs a ∣ Int.natAbs (a * b) := by
      rw [Int.natAbs_mul]
      exact dvd_mul_right _ _
    have gcd_dvd : Int.gcd (Int.natAbs a) (Int.natAbs b) ∣ Int.natAbs a := Int.gcd_dvd_left _ _
    exact Nat.dvd_div_of_mul_dvd gcd_dvd this

/- LLM HELPER -/
lemma dvd_lcm_right (a b : Int) : b ∣ lcmInt a b := by
  unfold lcmInt
  split_ifs with h
  · cases h with
    | mk ha hb =>
      rw [hb]
      exact dvd_zero _
  · have h_not_both_zero : a ≠ 0 ∨ b ≠ 0 := by
      push_neg at h
      exact h
    unfold gcdInt
    rw [Int.dvd_iff_natAbs_dvd_natAbs]
    have : Int.natAbs b ∣ Int.natAbs (a * b) := by
      rw [Int.natAbs_mul]
      exact dvd_mul_left _ _
    have gcd_dvd : Int.gcd (Int.natAbs a) (Int.natAbs b) ∣ Int.natAbs b := Int.gcd_dvd_right _ _
    exact Nat.dvd_div_of_mul_dvd gcd_dvd this

/- LLM HELPER -/
lemma lcm_minimal (a b m : Int) (hm_pos : m > 0) (ha : m % a = 0) (hb : m % b = 0) : 
  lcmInt a b ≤ m := by
  unfold lcmInt
  split_ifs with h
  · cases h with
    | mk ha_zero hb_zero =>
      rw [ha_zero, hb_zero] at ha hb
      simp at ha hb
      exact le_of_lt hm_pos
  · have h_not_both_zero : a ≠ 0 ∨ b ≠ 0 := by
      push_neg at h
      exact h
    have ha_dvd : a ∣ m := Int.dvd_iff_mod_eq_zero.mpr ha
    have hb_dvd : b ∣ m := Int.dvd_iff_mod_eq_zero.mpr hb
    cases h_not_both_zero with
    | inl ha_ne_zero =>
      have : Int.natAbs a > 0 := Int.natAbs_pos.mpr ha_ne_zero
      have m_pos_nat : Int.natAbs m > 0 := Int.natAbs_pos.mpr (ne_of_gt hm_pos)
      rw [Int.dvd_iff_natAbs_dvd_natAbs] at ha_dvd hb_dvd
      have : Int.natAbs (lcmInt a b) ≤ Int.natAbs m := by
        rw [Int.natAbs_of_nonneg (lcm_nonneg a b)]
        unfold lcmInt
        split_ifs
        · exact Nat.zero_le _
        · unfold gcdInt
          exact Nat.lcm_dvd_iff.mp ⟨ha_dvd, hb_dvd⟩
      exact Int.natAbs_le_iff_sq_le_sq.mp this
    | inr hb_ne_zero =>
      have : Int.natAbs b > 0 := Int.natAbs_pos.mpr hb_ne_zero
      have m_pos_nat : Int.natAbs m > 0 := Int.natAbs_pos.mpr (ne_of_gt hm_pos)
      rw [Int.dvd_iff_natAbs_dvd_natAbs] at ha_dvd hb_dvd
      have : Int.natAbs (lcmInt a b) ≤ Int.natAbs m := by
        rw [Int.natAbs_of_nonneg (lcm_nonneg a b)]
        unfold lcmInt
        split_ifs
        · exact Nat.zero_le _
        · unfold gcdInt
          exact Nat.lcm_dvd_iff.mp ⟨ha_dvd, hb_dvd⟩
      exact Int.natAbs_le_iff_sq_le_sq.mp this

theorem lcmInt_spec (a b : Int) :
  lcmInt a b ≥ 0 ∧
  lcmInt a b % a = 0 ∧
  lcmInt a b % b = 0 ∧
  ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m := by
  constructor
  · exact lcm_nonneg a b
  constructor
  · exact Int.mod_eq_zero_of_dvd (dvd_lcm_left a b)
  constructor
  · exact Int.mod_eq_zero_of_dvd (dvd_lcm_right a b)
  · exact lcm_minimal a b

end NpLcm