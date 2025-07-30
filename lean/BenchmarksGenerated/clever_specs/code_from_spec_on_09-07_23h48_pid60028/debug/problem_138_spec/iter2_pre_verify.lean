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
in
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma even_zero : Even (0 : Nat) := by
  use 0
  simp

-- LLM HELPER
lemma sum_four_evens_even (a b c d : Nat) (ha : Even a) (hb : Even b) (hc : Even c) (hd : Even d) :
  Even (a + b + c + d) := by
  obtain ⟨k₁, hk₁⟩ := ha
  obtain ⟨k₂, hk₂⟩ := hb
  obtain ⟨k₃, hk₃⟩ := hc
  obtain ⟨k₄, hk₄⟩ := hd
  use k₁ + k₂ + k₃ + k₄
  rw [hk₁, hk₂, hk₃, hk₄]
  ring

-- LLM HELPER
lemma int_even_iff_nat_even (n : Nat) : Even (n : Int) ↔ Even n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    if h_pos : 0 ≤ k then
      use Int.natAbs k
      rw [← Int.natCast_inj] at hk
      simp at hk
      rw [Int.natAbs_of_nonneg h_pos] at hk
      exact hk
    else
      push_neg at h_pos
      have : k < 0 := h_pos
      have : n = Int.natAbs k + Int.natAbs k := by
        rw [← hk]
        rw [Int.natAbs_of_neg this]
        ring
      rw [this]
      use Int.natAbs k
      ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    rw [hk]
    simp

def implementation (n: Int) : Bool :=
  if n < 0 then false
  else if n % 2 = 1 then false
  else true

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp [problem_spec]
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro h
      split_ifs at h with h1 h2
      · contradiction
      · contradiction
      · -- h : true, need to prove ∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ a + b + c + d = n
        push_neg at h1
        have h_nonneg : 0 ≤ n := h1
        have h_even : Even n := by
          push_neg at h2
          rw [Int.emod_two_eq_zero] at h2
          exact h2
        -- Convert to natural number
        have n_nat : Nat := Int.natAbs n
        have h_n_eq : n = n_nat := by
          rw [Int.natAbs_of_nonneg h_nonneg]
        have h_even_nat : Even n_nat := by
          rw [← h_n_eq]
          rw [int_even_iff_nat_even]
          exact h_even
        -- Use 0, 0, 0, n_nat
        use 0, 0, 0, n_nat
        constructor
        · exact even_zero
        constructor
        · exact even_zero
        constructor
        · exact even_zero
        constructor
        · exact h_even_nat
        · simp [h_n_eq]
    · intro h
      obtain ⟨a, b, c, d, ha, hb, hc, hd, h_sum⟩ := h
      split_ifs with h1 h2
      · -- Case n < 0, but sum of naturals equals n
        have : 0 ≤ n := by
          rw [← h_sum]
          simp
        linarith
      · -- Case n ≥ 0 but n % 2 = 1
        have h_even : Even n := by
          rw [← h_sum]
          simp
          exact sum_four_evens_even a b c d ha hb hc hd
        rw [Int.even_iff_two_dvd] at h_even
        rw [Int.dvd_iff_emod_eq_zero] at h_even
        rw [h_even] at h2
        simp at h2
      · -- Case n ≥ 0 and n % 2 = 0
        trivial