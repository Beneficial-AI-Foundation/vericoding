namespace NpGcd

-- LLM HELPER
def gcdNat (a b : Nat) : Nat := Nat.gcd a b

-- LLM HELPER
def intAbs (n : Int) : Nat :=
  if n ≥ 0 then n.natAbs else (-n).natAbs

def gcdInt (a b : Int) : Int := (gcdNat (intAbs a) (intAbs b) : Int)

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
  simp [gcdInt]
  rw [← intAbs_spec, ← intAbs_spec]
  have h := Nat.gcd_dvd_left (Int.natAbs a) (Int.natAbs b)
  have : (Int.natAbs a : Int) % (Nat.gcd (Int.natAbs a) (Int.natAbs b) : Int) = 0 := by
    rw [Int.coe_nat_mod]
    simp [Nat.mod_eq_zero_of_dvd h]
  rw [← Int.natAbs_of_nonneg (Int.natAbs_nonneg a)] at this
  exact Int.mod_two_eq_zero_or_one.elim (fun _ => this) (fun _ => this)

-- LLM HELPER
lemma gcdInt_dvd_right (a b : Int) : b % gcdInt a b = 0 := by
  simp [gcdInt]
  rw [← intAbs_spec, ← intAbs_spec]
  have h := Nat.gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  have : (Int.natAbs b : Int) % (Nat.gcd (Int.natAbs a) (Int.natAbs b) : Int) = 0 := by
    rw [Int.coe_nat_mod]
    simp [Nat.mod_eq_zero_of_dvd h]
  rw [← Int.natAbs_of_nonneg (Int.natAbs_nonneg b)] at this
  exact Int.mod_two_eq_zero_or_one.elim (fun _ => this) (fun _ => this)

-- LLM HELPER
lemma gcdInt_greatest (a b d : Int) : d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  intro hd_pos ha hb
  simp [gcdInt]
  have ha_dvd : Int.natAbs d ∣ Int.natAbs a := by
    have : d ∣ a := Int.dvd_iff_mod_eq_zero.mpr ha
    exact Int.natAbs_dvd_iff_dvd.mpr this
  have hb_dvd : Int.natAbs d ∣ Int.natAbs b := by
    have : d ∣ b := Int.dvd_iff_mod_eq_zero.mpr hb
    exact Int.natAbs_dvd_iff_dvd.mpr this
  have h := Nat.dvd_gcd_iff.mpr ⟨ha_dvd, hb_dvd⟩
  rw [← Int.natAbs_of_nonneg (le_of_lt hd_pos)]
  exact Int.coe_nat_le_coe_nat_of_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (Int.natAbs a) (Int.natAbs_pos_of_ne_zero (ne_of_gt (Int.natAbs_pos_of_ne_zero (ne_of_gt hd_pos))))) h)

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  exact ⟨gcdInt_nonneg a b, gcdInt_dvd_left a b, gcdInt_dvd_right a b, gcdInt_greatest a b⟩

end NpGcd