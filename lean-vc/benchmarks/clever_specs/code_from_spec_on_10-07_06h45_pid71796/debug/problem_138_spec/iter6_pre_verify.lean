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
def EvenInt (n : Int) : Prop := ∃ k : Int, n = 2 * k

-- LLM HELPER
def EvenIntDecidable (n : Int) : Bool := decide (n % 2 = 0)

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
  EvenInt (a + b + c + d) := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  obtain ⟨kc, rfl⟩ := hc
  obtain ⟨kd, rfl⟩ := hd
  use ka + kb + kc + kd
  simp only [Int.coe_nat_add, Int.coe_nat_mul]
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
lemma odd_int_not_sum_four_evens (n : Int) (hn : ¬EvenInt n) : 
  ¬∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n) := by
  intro ⟨a, b, c, d, ha, hb, hc, hd, h⟩
  have h_even : EvenInt (a + b + c + d) := sum_four_evens_even a b c d ha hb hc hd
  rw [h] at h_even
  exact hn h_even

-- LLM HELPER
lemma nonneg_even_sum_four_evens (n : Int) (hn_nonneg : n ≥ 0) (hn_even : EvenInt n) : 
  ∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ (a + b + c + d = n) := by
  obtain ⟨k, hk⟩ := hn_even
  have n_nat : ∃ m : Nat, n = ↑m := by
    rw [hk]
    by_cases h : k ≥ 0
    · obtain ⟨k_nat, hk_nat⟩ := Int.eq_coe_of_zero_le h
      use 2 * k_nat
      simp only [Int.coe_nat_mul]
      rw [hk_nat]
    · exfalso
      have : n < 0 := by
        rw [hk]
        exact Int.mul_neg_of_pos_of_neg (by norm_num : (0 : Int) < 2) (not_le.mp h)
      exact not_le.mpr this hn_nonneg
  obtain ⟨m, hm⟩ := n_nat
  rw [hm] at hk
  have : (m : Int) = 2 * k := hk
  have k_nonneg : k ≥ 0 := by
    have : (0 : Int) ≤ 2 * k := by rw [←this]; exact Int.coe_nat_nonneg _
    exact Int.mul_nonneg_iff_of_pos_left (by norm_num : (0 : Int) < 2) |>.mp this
  obtain ⟨k_nat, hk_nat⟩ := Int.eq_coe_of_zero_le k_nonneg
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

-- LLM HELPER
lemma evenint_decidable_correct (n : Int) : EvenIntDecidable n = true ↔ EvenInt n := by
  simp only [EvenIntDecidable, EvenInt]
  constructor
  · intro h
    simp only [decide_eq_true_eq] at h
    simp only [Int.mod_two_eq_zero] at h
    exact h
  · intro h
    simp only [decide_eq_true_eq]
    simp only [Int.mod_two_eq_zero]
    exact h

def implementation (n: Int) : Bool := 
  decide (n ≥ 0) && (EvenIntDecidable n)

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp only [problem_spec, implementation]
  use decide (n ≥ 0) && (EvenIntDecidable n)
  constructor
  · rfl
  · simp only [Bool.true_eq]
    constructor
    · intro h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hn_nonneg, hn_even⟩ := h
      simp only [decide_eq_true_eq] at hn_nonneg
      have hn_even_int : EvenInt n := (evenint_decidable_correct n).mp hn_even
      exact nonneg_even_sum_four_evens n hn_nonneg hn_even_int
    · intro ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩
      simp only [Bool.and_eq_true]
      constructor
      · simp only [decide_eq_true_eq]
        rw [←h_sum]
        exact Int.coe_nat_nonneg _
      · rw [←h_sum]
        have h_even : EvenInt (a + b + c + d) := sum_four_evens_even a b c d ha hb hc hd
        exact (evenint_decidable_correct (a + b + c + d)).mpr h_even