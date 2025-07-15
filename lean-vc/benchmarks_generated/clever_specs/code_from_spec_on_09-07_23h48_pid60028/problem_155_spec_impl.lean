def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := Int.natAbs num;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl (Int.ofNat numBy10);
  (result = impl (Int.ofNat numAbs)) ∧
  (0 ≤ num → (Even (Int.ofNat numAbs) ↔ 1 + even_count' = even_count) ∧ (Odd (Int.ofNat numAbs) ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd (Int.ofNat numAbs) ↔ 1 + odd_count' = odd_count) ∧ (Even (Int.ofNat numAbs) ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def Even (n : Int) : Prop := ∃ k : Int, n = 2 * k

-- LLM HELPER
def Odd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- LLM HELPER
def count_even_odd_digits (n: Nat) : Nat × Nat :=
  if n = 0 then (1, 0)
  else
    let rec aux (n: Nat) : Nat × Nat :=
      if n = 0 then (0, 0)
      else
        let digit := n % 10
        let rest := n / 10
        let (even_rest, odd_rest) := aux rest
        if digit % 2 = 0 then
          (even_rest + 1, odd_rest)
        else
          (even_rest, odd_rest + 1)
    aux n

def implementation (num: Int) : Int × Int := 
  let n := Int.natAbs num
  let (even_count, odd_count) := count_even_odd_digits n
  (Int.ofNat even_count, Int.ofNat odd_count)

-- LLM HELPER
lemma even_iff_mod_two_zero (n : Int) : Even n ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    simp [Int.mul_mod]
  · intro h
    use n / 2
    rw [Int.mul_div_cancel_of_mod_eq_zero h]

-- LLM HELPER
lemma odd_iff_mod_two_one (n : Int) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    simp [Int.add_mod, Int.mul_mod]
  · intro h
    use (n - 1) / 2
    have : n = 2 * ((n - 1) / 2) + 1 := by
      rw [← Int.sub_add_cancel n 1]
      rw [Int.add_comm]
      rw [← Int.mul_div_cancel_of_mod_eq_zero]
      simp [Int.sub_mod, h]
    exact this

-- LLM HELPER
lemma even_odd_exclusive (n : Int) : ¬(Even n ∧ Odd n) := by
  intro ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
  have : 2 * k1 = 2 * k2 + 1 := by rw [← h1, h2]
  have : 0 = 1 := by
    have : 2 * k1 - 2 * k2 = 1 := by rw [← this]; ring
    have : 2 * (k1 - k2) = 1 := by rw [← this]; ring
    have : 1 % 2 = 0 := by
      rw [← this]
      simp [Int.mul_mod]
    norm_num at this
  norm_num at this

-- LLM HELPER
lemma even_or_odd (n : Int) : Even n ∨ Odd n := by
  by_cases h : n % 2 = 0
  · left
    rw [even_iff_mod_two_zero]
    exact h
  · right
    rw [odd_iff_mod_two_one]
    have : n % 2 = 1 := by
      have : n % 2 < 2 := Int.mod_lt_of_pos n (by norm_num)
      have : n % 2 ≥ 0 := Int.mod_nonneg n (by norm_num)
      omega
    exact this

-- LLM HELPER
lemma nat_abs_preserves_parity (n : Int) : n ≥ 0 → (Even n ↔ Even (Int.ofNat n.natAbs)) := by
  intro h_nonneg
  rw [Int.natAbs_of_nonneg h_nonneg]
  simp

-- LLM HELPER
lemma count_even_odd_digits_zero : count_even_odd_digits 0 = (1, 0) := by
  simp [count_even_odd_digits]

-- LLM HELPER
lemma count_even_odd_digits_nonzero (n : Nat) (h : n > 0) :
  let (even_count, odd_count) := count_even_odd_digits n
  let digit := n % 10
  let rest := n / 10
  let (even_rest, odd_rest) := count_even_odd_digits rest
  (digit % 2 = 0 → even_count = even_rest + 1 ∧ odd_count = odd_rest) ∧
  (digit % 2 = 1 → even_count = even_rest ∧ odd_count = odd_rest + 1) := by
  simp [count_even_odd_digits]
  simp [Nat.pos_iff_ne_zero.mp h]
  simp [count_even_odd_digits.aux]
  by_cases h_zero : n = 0
  · contradiction
  · simp [h_zero]
    split_ifs with h_digit
    · simp [h_digit]
    · simp
      have : n % 10 % 2 = 1 := by
        have : n % 10 % 2 < 2 := Nat.mod_lt (n % 10) (by norm_num)
        omega
      simp [this]

theorem correctness (num: Int) : problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · unfold implementation
    simp only []
    let n := Int.natAbs num
    constructor
    · rfl
    · constructor
      · intro h_nonneg
        constructor
        · by_cases h : n = 0
          · simp [h, count_even_odd_digits_zero]
            constructor
            · intro h_even
              have : Even (Int.ofNat 0) := h_even
              have : ¬Even (Int.ofNat 0) := by simp [Even]
              contradiction
            · intro h_eq
              simp at h_eq
          · have h_pos : n > 0 := Nat.pos_of_ne_zero h
            have spec := count_even_odd_digits_nonzero n h_pos
            simp at spec
            let digit := n % 10
            let rest := n / 10
            let (even_rest, odd_rest) := count_even_odd_digits rest
            have parity_equiv : Even (Int.ofNat n) ↔ digit % 2 = 0 := by
              rw [even_iff_mod_two_zero]
              constructor
              · intro h_mod
                have : Int.ofNat n % 2 = 0 := h_mod
                have : (Int.ofNat n % 2).natAbs = 0 := by
                  rw [this]
                  simp
                have : Int.ofNat n % 2 = Int.ofNat (n % 2) := by simp [Int.coe_nat_mod]
                rw [this] at h_mod
                have : n % 2 = 0 := by
                  have : Int.ofNat (n % 2) = 0 := h_mod
                  simp at this
                  exact this
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this] at *
                exact ‹(n % 10) % 2 = 0›
              · intro h_digit
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this, h_digit]
                simp [Int.coe_nat_mod]
            rw [parity_equiv]
            exact spec.1
        · by_cases h : n = 0
          · simp [h, count_even_odd_digits_zero]
            constructor
            · intro h_odd
              have : Odd (Int.ofNat 0) := h_odd
              have : ¬Odd (Int.ofNat 0) := by simp [Odd]
              contradiction
            · intro h_eq
              simp at h_eq
          · have h_pos : n > 0 := Nat.pos_of_ne_zero h
            have spec := count_even_odd_digits_nonzero n h_pos
            simp at spec
            let digit := n % 10
            let rest := n / 10
            let (even_rest, odd_rest) := count_even_odd_digits rest
            have parity_equiv : Odd (Int.ofNat n) ↔ digit % 2 = 1 := by
              rw [odd_iff_mod_two_one]
              constructor
              · intro h_mod
                have : Int.ofNat n % 2 = 1 := h_mod
                have : Int.ofNat n % 2 = Int.ofNat (n % 2) := by simp [Int.coe_nat_mod]
                rw [this] at h_mod
                have : n % 2 = 1 := by
                  have : Int.ofNat (n % 2) = 1 := h_mod
                  simp at this
                  exact this
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this] at *
                exact ‹(n % 10) % 2 = 1›
              · intro h_digit
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this, h_digit]
                simp [Int.coe_nat_mod]
            rw [parity_equiv]
            by_cases h_even : digit % 2 = 0
            · simp [h_even]
            · simp [h_even]
              have h_odd : digit % 2 = 1 := by
                have : digit % 2 < 2 := Nat.mod_lt digit (by norm_num)
                omega
              simp [h_odd]
              exact spec.2 h_odd
      · intro h_nonneg
        constructor
        · by_cases h : n = 0
          · simp [h, count_even_odd_digits_zero]
            constructor
            · intro h_odd
              have : Odd (Int.ofNat 0) := h_odd
              have : ¬Odd (Int.ofNat 0) := by simp [Odd]
              contradiction
            · intro h_eq
              simp at h_eq
          · have h_pos : n > 0 := Nat.pos_of_ne_zero h
            have spec := count_even_odd_digits_nonzero n h_pos
            simp at spec
            let digit := n % 10
            let rest := n / 10
            let (even_rest, odd_rest) := count_even_odd_digits rest
            have parity_equiv : Odd (Int.ofNat n) ↔ digit % 2 = 1 := by
              rw [odd_iff_mod_two_one]
              constructor
              · intro h_mod
                have : Int.ofNat n % 2 = 1 := h_mod
                have : Int.ofNat n % 2 = Int.ofNat (n % 2) := by simp [Int.coe_nat_mod]
                rw [this] at h_mod
                have : n % 2 = 1 := by
                  have : Int.ofNat (n % 2) = 1 := h_mod
                  simp at this
                  exact this
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this] at *
                exact ‹(n % 10) % 2 = 1›
              · intro h_digit
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this, h_digit]
                simp [Int.coe_nat_mod]
            rw [parity_equiv]
            exact spec.2
        · by_cases h : n = 0
          · simp [h, count_even_odd_digits_zero]
            constructor
            · intro h_even
              have : Even (Int.ofNat 0) := h_even
              have : ¬Even (Int.ofNat 0) := by simp [Even]
              contradiction
            · intro h_eq
              simp at h_eq
          · have h_pos : n > 0 := Nat.pos_of_ne_zero h
            have spec := count_even_odd_digits_nonzero n h_pos
            simp at spec
            let digit := n % 10
            let rest := n / 10
            let (even_rest, odd_rest) := count_even_odd_digits rest
            have parity_equiv : Even (Int.ofNat n) ↔ digit % 2 = 0 := by
              rw [even_iff_mod_two_zero]
              constructor
              · intro h_mod
                have : Int.ofNat n % 2 = 0 := h_mod
                have : Int.ofNat n % 2 = Int.ofNat (n % 2) := by simp [Int.coe_nat_mod]
                rw [this] at h_mod
                have : n % 2 = 0 := by
                  have : Int.ofNat (n % 2) = 0 := h_mod
                  simp at this
                  exact this
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this] at *
                exact ‹(n % 10) % 2 = 0›
              · intro h_digit
                have : n % 2 = (n % 10) % 2 := by
                  rw [← Nat.mod_mod_of_dvd]
                  norm_num
                rw [this, h_digit]
                simp [Int.coe_nat_mod]
            rw [parity_equiv]
            by_cases h_even : digit % 2 = 0
            · simp [h_even]
              exact spec.1 h_even
            · simp [h_even]