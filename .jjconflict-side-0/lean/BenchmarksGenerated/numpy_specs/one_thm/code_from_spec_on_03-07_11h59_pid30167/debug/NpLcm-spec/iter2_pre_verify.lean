namespace NpLcm

/- LLM HELPER -/
def gcdInt (a b : Int) : Int :=
  Int.gcd (Int.natAbs a) (Int.natAbs b)

/- LLM HELPER -/
lemma gcdInt_pos (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : gcdInt a b > 0 := by
  unfold gcdInt
  apply Int.coe_nat_pos.mpr
  apply Nat.gcd_pos_of_pos_left_or_pos_right
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
lemma lcmInt_nonneg (a b : Int) : lcmInt a b ≥ 0 := by
  unfold lcmInt
  split_ifs with h
  · norm_num
  · apply Int.div_nonneg
    · exact Int.natAbs_nonneg _
    · apply Int.coe_nat_nonneg

/- LLM HELPER -/
lemma gcdInt_dvd_left (a b : Int) : gcdInt a b ∣ a := by
  unfold gcdInt
  have h := Int.gcd_dvd_left (Int.natAbs a) (Int.natAbs b)
  rw [Int.coe_nat_dvd] at h
  exact Int.dvd_of_natAbs_dvd h

/- LLM HELPER -/
lemma gcdInt_dvd_right (a b : Int) : gcdInt a b ∣ b := by
  unfold gcdInt
  have h := Int.gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  rw [Int.coe_nat_dvd] at h
  exact Int.dvd_of_natAbs_dvd h

/- LLM HELPER -/
lemma lcmInt_dvd_left (a b : Int) : a ∣ lcmInt a b := by
  unfold lcmInt
  split_ifs with h
  · cases h with
    | mk ha hb =>
      rw [ha]
      simp
  · push_neg at h
    have ha_or_hb : a ≠ 0 ∨ b ≠ 0 := h
    have hgcd_pos : gcdInt a b > 0 := gcdInt_pos a b ha_or_hb
    have hgcd_dvd_a : gcdInt a b ∣ a := gcdInt_dvd_left a b
    obtain ⟨k, hk⟩ := hgcd_dvd_a
    rw [hk]
    have : Int.natAbs (a * b) = Int.natAbs a * Int.natAbs b := Int.natAbs_mul a b
    rw [this, hk]
    have : Int.natAbs (gcdInt a b * k) = Int.natAbs (gcdInt a b) * Int.natAbs k := Int.natAbs_mul (gcdInt a b) k
    rw [this]
    have hgcd_nat : Int.natAbs (gcdInt a b) = gcdInt a b := by
      rw [Int.natAbs_of_nonneg (le_of_lt hgcd_pos)]
    rw [hgcd_nat]
    have : gcdInt a b * k ∣ gcdInt a b * Int.natAbs k * Int.natAbs b / gcdInt a b := by
      rw [← Int.mul_div_assoc]
      apply dvd_mul_right
      rw [Int.mul_comm (Int.natAbs k)]
      apply dvd_mul_right
    exact this

/- LLM HELPER -/
lemma lcmInt_dvd_right (a b : Int) : b ∣ lcmInt a b := by
  unfold lcmInt
  split_ifs with h
  · cases h with
    | mk ha hb =>
      rw [hb]
      simp
  · push_neg at h
    have ha_or_hb : a ≠ 0 ∨ b ≠ 0 := h
    have hgcd_pos : gcdInt a b > 0 := gcdInt_pos a b ha_or_hb
    have hgcd_dvd_b : gcdInt a b ∣ b := gcdInt_dvd_right a b
    obtain ⟨k, hk⟩ := hgcd_dvd_b
    rw [hk]
    have : Int.natAbs (a * b) = Int.natAbs a * Int.natAbs b := Int.natAbs_mul a b
    rw [this, hk]
    have : Int.natAbs (gcdInt a b * k) = Int.natAbs (gcdInt a b) * Int.natAbs k := Int.natAbs_mul (gcdInt a b) k
    rw [this]
    have hgcd_nat : Int.natAbs (gcdInt a b) = gcdInt a b := by
      rw [Int.natAbs_of_nonneg (le_of_lt hgcd_pos)]
    rw [hgcd_nat]
    have : gcdInt a b * k ∣ Int.natAbs a * gcdInt a b * Int.natAbs k / gcdInt a b := by
      rw [← Int.mul_div_assoc]
      apply dvd_mul_right
      rw [Int.mul_comm (Int.natAbs a)]
      apply dvd_mul_right
    exact this

theorem lcmInt_spec (a b : Int) :
  lcmInt a b ≥ 0 ∧
  lcmInt a b % a = 0 ∧
  lcmInt a b % b = 0 ∧
  ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m := by
  constructor
  · exact lcmInt_nonneg a b
  constructor
  · if h : a = 0 then
      simp [h]
      unfold lcmInt
      simp
    else
      have : a ∣ lcmInt a b := lcmInt_dvd_left a b
      exact Int.dvd_iff_mod_eq_zero.mp this
  constructor
  · if h : b = 0 then
      simp [h]
      unfold lcmInt
      simp
    else
      have : b ∣ lcmInt a b := lcmInt_dvd_right a b
      exact Int.dvd_iff_mod_eq_zero.mp this
  · intro m hm_pos hm_a hm_b
    if h : a = 0 ∧ b = 0 then
      cases h with
      | intro ha hb =>
        unfold lcmInt
        simp [ha, hb]
        exact le_of_lt hm_pos
    else
      push_neg at h
      have ha_or_hb : a ≠ 0 ∨ b ≠ 0 := h
      unfold lcmInt
      simp [h]
      have hgcd_pos : gcdInt a b > 0 := gcdInt_pos a b ha_or_hb
      have hm_a_dvd : a ∣ m := Int.dvd_iff_mod_eq_zero.mpr hm_a
      have hm_b_dvd : b ∣ m := Int.dvd_iff_mod_eq_zero.mpr hm_b
      have lcm_dvd_m : lcmInt a b ∣ m := by
        simp [lcmInt, h]
        apply Int.dvd_div_of_mul_dvd
        rw [Int.mul_comm]
        have : Int.natAbs (a * b) = Int.natAbs a * Int.natAbs b := Int.natAbs_mul a b
        rw [this]
        have : Int.natAbs a * Int.natAbs b ∣ Int.natAbs (m * gcdInt a b) := by
          rw [Int.natAbs_mul]
          apply Int.mul_dvd_of_dvd_each
          · exact Int.natAbs_dvd_of_dvd hm_a_dvd
          · exact Int.natAbs_dvd_of_dvd hm_b_dvd
        exact this
      exact Int.le_of_dvd hm_pos lcm_dvd_m

end NpLcm