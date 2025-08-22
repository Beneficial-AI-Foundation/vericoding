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
      sorry

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
      sorry

/- LLM HELPER -/
lemma lcmInt_dvd_of_dvd (a b m : Int) (hm : m > 0) (ha : a ∣ m) (hb : b ∣ m) : lcmInt a b ∣ m := by
  unfold lcmInt
  by_cases h : a = 0 ∧ b = 0
  · simp [h]
    exact Int.dvd_zero m
  · simp [h]
    sorry

theorem lcmInt_spec (a b : Int) :
  lcmInt a b ≥ 0 ∧
  lcmInt a b % a = 0 ∧
  lcmInt a b % b = 0 ∧
  ∀ m : Int, m > 0 → m % a = 0 → m % b = 0 → lcmInt a b ≤ m := by
  constructor
  · exact lcmInt_nonneg a b
  constructor
  · rw [Int.mod_eq_zero_iff_dvd]
    exact dvd_lcmInt_left a b
  constructor
  · rw [Int.mod_eq_zero_iff_dvd]
    exact dvd_lcmInt_right a b
  · intro m hm hma hmb
    rw [Int.mod_eq_zero_iff_dvd] at hma hmb
    have hlcm_dvd_m : lcmInt a b ∣ m := lcmInt_dvd_of_dvd a b m hm hma hmb
    exact Int.le_of_dvd hm hlcm_dvd_m

end NpLcm