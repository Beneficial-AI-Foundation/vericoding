def problem_spec
-- function signature
(impl: Int → Bool)
-- inputs
(n: Int) :=
-- spec
let spec (result: Bool) :=
  let sum_exists := ∃ a b c d : Nat,
    Even a ∧
    Even b ∧
    Even c ∧
    Even d ∧
    (a + b + c + d = n);
  result = true ↔ sum_exists
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def Even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

-- LLM HELPER
lemma even_zero : Even 0 := ⟨0, rfl⟩

-- LLM HELPER
lemma even_two : Even 2 := ⟨1, rfl⟩

-- LLM HELPER
lemma even_four : Even 4 := ⟨2, rfl⟩

-- LLM HELPER
lemma even_six : Even 6 := ⟨3, rfl⟩

-- LLM HELPER
lemma even_eight : Even 8 := ⟨4, rfl⟩

-- LLM HELPER
lemma sum_four_evens_even (a b c d : Nat) (ha : Even a) (hb : Even b) (hc : Even c) (hd : Even d) : 
  Even (a + b + c + d) := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  obtain ⟨kc, rfl⟩ := hc
  obtain ⟨kd, rfl⟩ := hd
  use ka + kb + kc + kd
  ring

-- LLM HELPER
lemma negative_int_not_sum_four_evens (n : Int) (hn : n < 0) : 
  ¬∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n) := by
  intro ⟨a, b, c, d, _, _, _, _, h⟩
  have : (a + b + c + d : Int) ≥ 0 := by
    simp only [Int.coe_nat_add]
    exact Int.coe_nat_nonneg _
  rw [←h] at this
  exact not_le.mpr hn this

-- LLM HELPER
lemma odd_int_not_sum_four_evens (n : Int) (hn : Odd n) : 
  ¬∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n) := by
  intro ⟨a, b, c, d, ha, hb, hc, hd, h⟩
  have h_even : Even (a + b + c + d) := sum_four_evens_even a b c d ha hb hc hd
  rw [h] at h_even
  obtain ⟨k, hk⟩ := hn
  obtain ⟨m, hm⟩ := h_even
  rw [hk] at hm
  have : Even (2 * k + 1) := ⟨m, hm⟩
  obtain ⟨j, hj⟩ := this
  have : 2 * k + 1 = 2 * j := hj
  have : 1 = 2 * j - 2 * k := by linarith
  have : 1 = 2 * (j - k) := by ring_nf at this ⊢; exact this
  have : Odd 1 := ⟨0, by norm_num⟩
  have : Even 1 := ⟨j - k, this.symm⟩
  obtain ⟨_, h1⟩ := this
  norm_num at h1

-- LLM HELPER
lemma nonneg_even_sum_four_evens (n : Int) (hn_nonneg : n ≥ 0) (hn_even : Even n) : 
  ∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n) := by
  obtain ⟨k, hk⟩ := hn_even
  have n_nat : ∃ m : Nat, n = ↑m := by
    exact Int.coe_nat_iff.mp ⟨hn_nonneg, hk ▸ dvd_refl _⟩
  obtain ⟨m, hm⟩ := n_nat
  rw [hm] at hk
  have : (m : Int) = 2 * k := hk
  have k_nonneg : k ≥ 0 := by
    have : (0 : Int) ≤ 2 * k := by rw [←this]; exact Int.coe_nat_nonneg _
    exact Int.mul_nonneg_iff_of_pos_left (by norm_num : (0 : Int) < 2) |>.mp this
  have : ∃ k_nat : Nat, k = ↑k_nat := Int.coe_nat_iff.mp ⟨k_nonneg, dvd_refl _⟩
  obtain ⟨k_nat, hk_nat⟩ := this
  rw [hk_nat] at hk
  have : (m : Int) = 2 * ↑k_nat := hk
  have : m = 2 * k_nat := by
    rw [Int.coe_nat_mul] at this
    exact Int.coe_nat_injective this
  use 2 * k_nat, 0, 0, 0
  constructor
  · exact ⟨k_nat, rfl⟩
  constructor
  · exact even_zero
  constructor
  · exact even_zero
  constructor
  · exact even_zero
  · simp only [add_zero]
    rw [hm, this]
    simp only [Int.coe_nat_mul]

def implementation (n: Int) : Bool := 
  n ≥ 0 ∧ Even n

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp only [problem_spec, implementation]
  use n ≥ 0 ∧ Even n
  constructor
  · rfl
  · intro result
    simp only [Bool.true_eq]
    constructor
    · intro h
      cases h with
      | inl h_pos_even =>
        obtain ⟨hn_nonneg, hn_even⟩ := h_pos_even
        exact nonneg_even_sum_four_evens n hn_nonneg hn_even
      | inr h_false =>
        exfalso
        exact h_false
    · intro ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩
      left
      constructor
      · rw [←h_sum]
        exact Int.coe_nat_nonneg _
      · rw [←h_sum]
        exact sum_four_evens_even a b c d ha hb hc hd