def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) : Prop :=
-- spec
let spec (result : Int) :=
  Int.natAbs result ≤ 81 ∧
  result % 10 = (a * b) % 10 ∧
  ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10))) ∧
  ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10))) ∧
  ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
-- program termination
∃ result,
  implementation a b = result ∧
  spec result

def implementation (a b: Int) : Int := 
  if (a % 10 = 0) ∨ (b % 10 = 0) then 0
  else (a % 10) * (b % 10)

-- LLM HELPER
lemma mod_10_range (x : Int) : -9 ≤ x % 10 ∧ x % 10 ≤ 9 := by
  have h1 : Int.natAbs (x % 10) < 10 := Int.natAbs_mod_lt x (by norm_num : (10 : Int) ≠ 0)
  have h2 : -10 < x % 10 := Int.neg_lt_of_natAbs_lt h1
  have h3 : x % 10 < 10 := Int.lt_of_natAbs_lt h1
  constructor
  · linarith
  · linarith

-- LLM HELPER
lemma natAbs_mul_mod_10_le_81 (a b : Int) : Int.natAbs ((a % 10) * (b % 10)) ≤ 81 := by
  have ha := mod_10_range a
  have hb := mod_10_range b
  have h_bound : Int.natAbs ((a % 10) * (b % 10)) ≤ 9 * 9 := by
    rw [Int.natAbs_mul]
    apply Nat.mul_le_mul'
    · cases' Int.le_or_gt (a % 10) 0 with h1 h2
      · rw [Int.natAbs_of_nonpos h1]
        linarith [ha.1]
      · rw [Int.natAbs_of_nonneg (Int.le_of_lt h2)]
        exact Int.natAbs_of_nonneg (Int.le_of_lt h2) ▸ ha.2
    · cases' Int.le_or_gt (b % 10) 0 with h1 h2
      · rw [Int.natAbs_of_nonpos h1]
        linarith [hb.1]
      · rw [Int.natAbs_of_nonneg (Int.le_of_lt h2)]
        exact Int.natAbs_of_nonneg (Int.le_of_lt h2) ▸ hb.2
  norm_num at h_bound
  exact h_bound

-- LLM HELPER
lemma mul_mod_eq (a b : Int) : (a % 10) * (b % 10) % 10 = (a * b) % 10 := by
  rw [← Int.mul_emod, Int.emod_emod_of_dvd, Int.emod_emod_of_dvd]
  · norm_num
  · norm_num

-- LLM HELPER
lemma div_mod_property (a b : Int) (ha : a % 10 ≠ 0) (hb : b % 10 ≠ 0) : 
  ((a % 10) * (b % 10)) / (b % 10) % 100 = (a % 10) := by
  have h_nonzero : b % 10 ≠ 0 := hb
  rw [Int.mul_ediv_cancel_left (a % 10) h_nonzero]
  have h_range := mod_10_range a
  have h_abs : Int.natAbs (a % 10) < 100 := by
    have : Int.natAbs (a % 10) ≤ 9 := by
      cases' Int.le_or_gt (a % 10) 0 with h1 h2
      · rw [Int.natAbs_of_nonpos h1]
        linarith [h_range.1]
      · rw [Int.natAbs_of_nonneg (Int.le_of_lt h2)]
        exact Int.natAbs_of_nonneg (Int.le_of_lt h2) ▸ h_range.2
    linarith
  exact Int.emod_eq_of_lt (Int.neg_lt_of_natAbs_lt h_abs) (Int.lt_of_natAbs_lt h_abs)

theorem correctness (a b: Int) : problem_spec implementation a b := by
  unfold problem_spec implementation
  simp only [exists_prop]
  by_cases h : (a % 10 = 0) ∨ (b % 10 = 0)
  · use 0
    constructor
    · simp [if_pos h]
    · constructor
      · norm_num
      · constructor
        · cases' h with ha hb
          · simp [ha, mul_zero, Int.zero_emod]
          · simp [hb, zero_mul, Int.zero_emod]
        · constructor
          · cases' h with ha hb
            · simp [ha, mul_zero, Int.zero_emod]
            · simp [hb, zero_mul, Int.zero_emod]
          · exact fun _ => rfl
  · use (a % 10) * (b % 10)
    constructor
    · simp [if_neg h]
    · constructor
      · exact natAbs_mul_mod_10_le_81 a b
      · constructor
        · exact mul_mod_eq a b
        · constructor
          · intro hb_nonzero
            constructor
            · exact dvd_mul_of_left dvd_refl (a % 10)
            · push_neg at h
              exact div_mod_property a b h.1 hb_nonzero
          · constructor
            · intro ha_nonzero
              constructor
              · exact dvd_mul_of_right dvd_refl (b % 10)
              · push_neg at h
                rw [mul_comm (a % 10) (b % 10)]
                exact div_mod_property b a h.2 ha_nonzero
            · intro h_contra
              contradiction