namespace NpGcd

-- LLM HELPER
def gcdNat (a b : Nat) : Nat := Nat.gcd a b

-- LLM HELPER
def intAbs (n : Int) : Nat :=
  if n ≥ 0 then n.natAbs else (-n).natAbs

def gcdInt (a b : Int) : Int := Int.natAbs (gcdNat (intAbs a) (intAbs b))

-- LLM HELPER
lemma gcdInt_nonneg (a b : Int) : gcdInt a b ≥ 0 := by
  simp [gcdInt]
  exact Int.natAbs_nonneg _

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
  rw [← Int.natAbs_of_nonneg (Int.natAbs_nonneg (Int.ofNat (Nat.gcd (Int.natAbs a) (Int.natAbs b))))]
  exact Int.dvd_iff_mod_eq_zero.mp (Int.natAbs_dvd_iff_dvd.mp h)

-- LLM HELPER
lemma gcdInt_dvd_right (a b : Int) : b % gcdInt a b = 0 := by
  simp [gcdInt]
  rw [← intAbs_spec, ← intAbs_spec]
  have h := Nat.gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  rw [← Int.natAbs_of_nonneg (Int.natAbs_nonneg (Int.ofNat (Nat.gcd (Int.natAbs a) (Int.natAbs b))))]
  exact Int.dvd_iff_mod_eq_zero.mp (Int.natAbs_dvd_iff_dvd.mp h)

-- LLM HELPER
lemma gcdInt_greatest (a b d : Int) : d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  intro hd_pos ha hb
  simp [gcdInt]
  have ha_dvd : Int.natAbs d ∣ Int.natAbs a := by
    rw [Int.natAbs_dvd_iff_dvd]
    exact Int.dvd_iff_mod_eq_zero.mpr ha
  have hb_dvd : Int.natAbs d ∣ Int.natAbs b := by
    rw [Int.natAbs_dvd_iff_dvd]
    exact Int.dvd_iff_mod_eq_zero.mpr hb
  have h := Nat.dvd_gcd_iff.mpr ⟨ha_dvd, hb_dvd⟩
  rw [← Int.natAbs_of_nonneg (le_of_lt hd_pos)]
  exact Int.natAbs_le_natAbs_of_le_of_dvd (Int.natAbs_nonneg _) h

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  exact ⟨gcdInt_nonneg a b, gcdInt_dvd_left a b, gcdInt_dvd_right a b, gcdInt_greatest a b⟩

end NpGcd