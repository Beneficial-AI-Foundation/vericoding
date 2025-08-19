def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) : Prop :=
-- spec
let spec (result : Int) :=
  abs result ≤ 81 ∧
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
  have h1 : abs (x % 10) < 10 := abs_emod_lt x (by norm_num : (10 : Int) ≠ 0)
  have h2 : -10 < x % 10 := neg_lt_of_abs_lt h1
  have h3 : x % 10 < 10 := lt_of_abs_lt h1
  constructor
  · linarith
  · linarith

-- LLM HELPER
lemma abs_mul_mod_10_le_81 (a b : Int) : abs ((a % 10) * (b % 10)) ≤ 81 := by
  have ha := mod_10_range a
  have hb := mod_10_range b
  have h_bound : abs ((a % 10) * (b % 10)) ≤ 9 * 9 := by
    rw [abs_mul]
    apply mul_le_mul'
    · cases' le_or_gt (a % 10) 0 with h1 h2
      · rw [abs_of_nonpos h1]
        linarith [ha.1]
      · rw [abs_of_pos h2]
        exact ha.2
    · cases' le_or_gt (b % 10) 0 with h1 h2
      · rw [abs_of_nonpos h1]
        linarith [hb.1]
      · rw [abs_of_pos h2]
        exact hb.2
  norm_num at h_bound
  exact h_bound

-- LLM HELPER
lemma mul_mod_eq (a b : Int) : (a % 10) * (b % 10) % 10 = (a * b) % 10 := by
  rw [← mul_emod, emod_emod_of_dvd, emod_emod_of_dvd]
  · norm_num
  · norm_num

-- LLM HELPER
lemma div_mod_property (a b : Int) (ha : a % 10 ≠ 0) (hb : b % 10 ≠ 0) : 
  ((a % 10) * (b % 10)) / (b % 10) % 100 = (a % 10) := by
  have h_nonzero : b % 10 ≠ 0 := hb
  rw [mul_ediv_cancel_left (a % 10) h_nonzero]
  have h_range := mod_10_range a
  have h_abs : abs (a % 10) < 100 := by
    have : abs (a % 10) ≤ 9 := by
      cases' abs_le.mp (abs_emod_lt a (by norm_num : (10 : Int) ≠ 0)) with h1 h2
      exact le_of_lt h2
    linarith
  exact emod_eq_of_lt (neg_lt_of_abs_lt h_abs) (lt_of_abs_lt h_abs)

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
          · simp [ha, mul_zero, zero_emod]
          · simp [hb, zero_mul, zero_emod]
        · constructor
          · cases' h with ha hb
            · simp [ha, mul_zero, zero_emod]
            · simp [hb, zero_mul, zero_emod]
          · exact fun _ => rfl
  · use (a % 10) * (b % 10)
    constructor
    · simp [if_neg h]
    · constructor
      · exact abs_mul_mod_10_le_81 a b
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