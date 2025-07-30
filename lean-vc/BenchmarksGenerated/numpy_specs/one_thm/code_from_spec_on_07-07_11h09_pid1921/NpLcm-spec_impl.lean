namespace NpLcm

-- LLM HELPER
def gcdInt (a b : Int) : Int :=
  Int.gcd a.natAbs b.natAbs

-- LLM HELPER
lemma gcdInt_pos (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : gcdInt a b > 0 := by
  unfold gcdInt
  apply Int.gcd_pos_of_pos_left
  cases h with
  | inl ha => 
    rw [Int.natAbs_pos]
    exact ha
  | inr hb =>
    rw [Int.natAbs_pos]
    exact hb

def lcmInt (a b : Int) : Int := 
  if a = 0 ∨ b = 0 then 0 else Int.natAbs (Int.natAbs a * Int.natAbs b / (Int.gcd a.natAbs b.natAbs))

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
  lcmInt a b = Int.natAbs (Int.natAbs a * Int.natAbs b / (Int.gcd a.natAbs b.natAbs)) := by
  unfold lcmInt
  simp [ha, hb]

-- LLM HELPER
lemma gcdInt_dvd_left (a b : Int) : Int.gcd a.natAbs b.natAbs ∣ Int.natAbs a := by
  exact Int.gcd_dvd_left a.natAbs b.natAbs

-- LLM HELPER
lemma gcdInt_dvd_right (a b : Int) : Int.gcd a.natAbs b.natAbs ∣ Int.natAbs b := by
  exact Int.gcd_dvd_right a.natAbs b.natAbs

-- LLM HELPER
lemma lcmInt_dvd_helper (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 
  a ∣ lcmInt a b ∧ b ∣ lcmInt a b := by
  constructor
  · rw [lcmInt_nonzero a b ha hb]
    have gcd_pos : Int.gcd a.natAbs b.natAbs > 0 := by
      apply Int.gcd_pos_of_pos_left
      rw [Int.natAbs_pos]
      exact ha
    rw [Int.dvd_iff_emod_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    use Int.natAbs (Int.natAbs b / Int.gcd a.natAbs b.natAbs)
    rw [Int.natAbs_mul]
    congr 1
    rw [Int.mul_ediv_cancel']
    exact Int.gcd_dvd_left a.natAbs b.natAbs
  · rw [lcmInt_nonzero a b ha hb]
    have gcd_pos : Int.gcd a.natAbs b.natAbs > 0 := by
      apply Int.gcd_pos_of_pos_right
      rw [Int.natAbs_pos]
      exact hb
    rw [Int.dvd_iff_emod_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    use Int.natAbs (Int.natAbs a / Int.gcd a.natAbs b.natAbs)
    rw [Int.natAbs_mul]
    congr 1
    rw [Int.mul_comm, Int.mul_ediv_cancel']
    exact Int.gcd_dvd_right a.natAbs b.natAbs

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
      exact Int.natAbs_nonneg _
  constructor
  · -- lcmInt a b % a = 0
    by_cases ha : a = 0
    · rw [ha, lcmInt_zero_left]
      simp
    · by_cases hb : b = 0
      · rw [hb, lcmInt_zero_right]
        simp
      · have hdvd := lcmInt_dvd_helper a b ha hb
        exact Int.emod_eq_zero_of_dvd hdvd.1
  constructor
  · -- lcmInt a b % b = 0
    by_cases hb : b = 0
    · rw [hb, lcmInt_zero_right]
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
        have gcd_pos : Int.gcd a.natAbs b.natAbs > 0 := by
          apply Int.gcd_pos_of_pos_left
          rw [Int.natAbs_pos]
          exact ha
        have h3 : Int.natAbs (Int.natAbs a * Int.natAbs b / Int.gcd a.natAbs b.natAbs) ≤ m := by
          have lcm_dvd : Int.natAbs (Int.natAbs a * Int.natAbs b / Int.gcd a.natAbs b.natAbs) ∣ m := by
            rw [Int.natAbs_dvd_iff_dvd]
            apply Int.dvd_of_mul_dvd_mul_left gcd_pos
            rw [Int.mul_ediv_cancel']
            exact Int.gcd_dvd_left a.natAbs b.natAbs
            exact Int.gcd_dvd_right a.natAbs b.natAbs
          exact Int.natAbs_le_of_dvd hm_pos lcm_dvd
        exact h3

end NpLcm