namespace NpGcd

-- LLM HELPER
def gcdNat (a b : Nat) : Nat := Nat.gcd a b

-- LLM HELPER
def intAbs (n : Int) : Nat :=
  if n ≥ 0 then n.natAbs else (-n).natAbs

def gcdInt (a b : Int) : Int := Int.ofNat (gcdNat (intAbs a) (intAbs b))

-- LLM HELPER
lemma gcdInt_nonneg (a b : Int) : gcdInt a b ≥ 0 := by
  simp [gcdInt]
  exact Int.coe_nat_nonneg _

-- LLM HELPER
lemma intAbs_spec (n : Int) : Int.natAbs n = intAbs n := by
  simp [intAbs]
  split_ifs with h
  · rfl
  · simp [Int.natAbs_neg]

-- LLM HELPER
lemma gcdInt_dvd_left (a b : Int) : a % gcdInt a b = 0 := by
  simp [gcdInt, gcdNat]
  rw [← intAbs_spec a, ← intAbs_spec b]
  have h := Nat.gcd_dvd_left (Int.natAbs a) (Int.natAbs b)
  have abs_dvd : (Nat.gcd (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs a : Int) := by
    rw [Int.coe_nat_dvd]
    exact h
  have sign_dvd : (Nat.gcd (Int.natAbs a) (Int.natAbs b) : Int) ∣ a := by
    rw [Int.dvd_iff_natAbs_dvd_natAbs]
    exact h
  exact Int.mod_eq_zero_of_dvd sign_dvd

-- LLM HELPER
lemma gcdInt_dvd_right (a b : Int) : b % gcdInt a b = 0 := by
  simp [gcdInt, gcdNat]
  rw [← intAbs_spec a, ← intAbs_spec b]
  have h := Nat.gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  have sign_dvd : (Nat.gcd (Int.natAbs a) (Int.natAbs b) : Int) ∣ b := by
    rw [Int.dvd_iff_natAbs_dvd_natAbs]
    exact h
  exact Int.mod_eq_zero_of_dvd sign_dvd

-- LLM HELPER
lemma gcdInt_greatest (a b d : Int) : d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  intro hd_pos ha hb
  simp [gcdInt, gcdNat]
  have ha_dvd : d ∣ a := Int.dvd_iff_mod_eq_zero.mpr ha
  have hb_dvd : d ∣ b := Int.dvd_iff_mod_eq_zero.mpr hb
  have ha_abs : Int.natAbs d ∣ Int.natAbs a := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact ha_dvd
  have hb_abs : Int.natAbs d ∣ Int.natAbs b := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact hb_dvd
  have h := Nat.dvd_gcd_iff.mpr ⟨ha_abs, hb_abs⟩
  rw [← Int.natAbs_of_nonneg (le_of_lt hd_pos)]
  exact Int.coe_nat_le_coe_nat_of_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (Int.natAbs a) (Int.natAbs_pos_of_ne_zero (ne_of_gt (Int.natAbs_pos_of_ne_zero (ne_of_gt hd_pos))))) h)

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  constructor
  · exact gcdInt_nonneg a b
  · constructor
    · exact gcdInt_dvd_left a b
    · constructor
      · exact gcdInt_dvd_right a b
      · exact gcdInt_greatest a b

end NpGcd