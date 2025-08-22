namespace NpLcm

/- LLM HELPER -/
def gcdInt (a b : Int) : Int :=
  Int.gcd (Int.natAbs a) (Int.natAbs b)

/- LLM HELPER -/
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
  if a = 0 ∧ b = 0 then 0
  else Int.natAbs (a * b) / gcdInt a b

/- LLM HELPER -/
lemma lcmInt_zero : lcmInt 0 0 = 0 := by
  unfold lcmInt
  simp

/- LLM HELPER -/
lemma lcmInt_nonneg (a b : Int) : lcmInt a b ≥ 0 := by
  unfold lcmInt
  by_cases h : a = 0 ∧ b = 0
  · simp [h]
  · simp [h]
    apply Int.div_nonneg
    · exact Int.natAbs_nonneg _
    · exact Int.coe_nat_nonneg _

/- LLM HELPER -/
lemma dvd_lcmInt_left (a b : Int) : a ∣ lcmInt a b := by
  unfold lcmInt
  by_cases h : a = 0 ∧ b = 0
  · simp [h]
  · simp [h]
    by_cases ha : a = 0
    · simp [ha]
    · have hg : gcdInt a b > 0 := gcdInt_pos a b (Or.inl ha)
      rw [Int.dvd_iff_emod_eq_zero]
      apply Int.emod_eq_zero_of_dvd
      use b / gcdInt a b
      simp [Int.mul_div_cancel_of_dvd]
      exact Int.gcd_dvd_left _ _

/- LLM HELPER -/
lemma dvd_lcmInt_right (a b : Int) : b ∣ lcmInt a b := by
  unfold lcmInt
  by_cases h : a = 0 ∧ b = 0
  · simp [h]
  · simp [h]
    by_cases hb : b = 0
    · simp [hb]
    · have hg : gcdInt a b > 0 := gcdInt_pos a b (Or.inr hb)
      rw [Int.dvd_iff_emod_eq_zero]
      apply Int.emod_eq_zero_of_dvd
      use a / gcdInt a b
      simp [Int.mul_div_cancel_of_dvd]
      exact Int.gcd_dvd_right _ _

/- LLM HELPER -/
lemma lcmInt_dvd_of_dvd (a b m : Int) (hm : m > 0) (ha : a ∣ m) (hb : b ∣ m) : lcmInt a b ∣ m := by
  unfold lcmInt
  by_cases h : a = 0 ∧ b = 0
  · simp [h]
    exact Int.dvd_zero m
  · simp [h]
    by_cases ha0 : a = 0
    · simp [ha0]
      exact hb
    · by_cases hb0 : b = 0
      · simp [hb0]
        exact ha
      · have hg : gcdInt a b > 0 := gcdInt_pos a b (Or.inl ha0)
        apply Int.dvd_of_emod_eq_zero
        rw [Int.emod_eq_zero_iff_dvd]
        use m / lcmInt a b
        rw [Int.mul_div_cancel_of_dvd]
        exact Int.dvd_refl _

/- LLM HELPER -/
lemma Int.emod_eq_zero_iff_dvd {a b : Int} : a % b = 0 ↔ b ∣ a := by
  constructor
  · intro h
    rw [Int.dvd_iff_emod_eq_zero]
    exact h
  · intro h
    rw [Int.dvd_iff_emod_eq_zero] at h
    exact h

theorem lcmInt_spec (a b : Int) :
  lcmInt a b ≥ 0 ∧
  lcmInt a b % a = 0 ∧
  lcmInt a b % b = 0 ∧
  ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m := by
  constructor
  · exact lcmInt_nonneg a b
  constructor
  · rw [Int.emod_eq_zero_iff_dvd]
    exact dvd_lcmInt_left a b
  constructor
  · rw [Int.emod_eq_zero_iff_dvd]
    exact dvd_lcmInt_right a b
  · intro m hm hma hmb
    rw [Int.emod_eq_zero_iff_dvd] at hma hmb
    have hlcm_dvd_m : lcmInt a b ∣ m := lcmInt_dvd_of_dvd a b m hm hma hmb
    exact Int.le_of_dvd hm hlcm_dvd_m

end NpLcm