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
lemma even_iff_mod_two_zero (n : Nat) : Even (Int.ofNat n) ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    have h_pos : 0 ≤ k := by
      have : 0 ≤ Int.ofNat n := Int.coe_nat_nonneg n
      rw [hk] at this
      exact Int.div_nonneg this (by norm_num)
    cases' Int.eq_coe_of_zero_le h_pos with m hm
    rw [hm] at hk
    have : n = (2 * m).natAbs := by
      rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
    rw [Int.natAbs_of_nonneg (by simp [Int.mul_nonneg_of_nonneg_of_nonneg (by norm_num) (Int.coe_nat_nonneg m)])] at this
    rw [Int.natCast_mul, Int.natCast_two] at this
    rw [← this]
    simp [Nat.mul_mod]
  · intro h
    use Int.ofNat (n / 2)
    simp [Int.ofNat_mul]
    have : n = 2 * (n / 2) := by
      rw [← Nat.two_mul_div_two_of_even]
      rw [Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      exact h
    rw [← Int.coe_nat_mul, ← this]

-- LLM HELPER
lemma odd_iff_mod_two_one (n : Nat) : Odd (Int.ofNat n) ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    have h_pos : 0 ≤ k := by
      have : 0 ≤ Int.ofNat n := Int.coe_nat_nonneg n
      rw [hk] at this
      omega
    cases' Int.eq_coe_of_zero_le h_pos with m hm
    rw [hm] at hk
    have : n = (2 * m + 1).natAbs := by
      rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
    rw [Int.natAbs_of_nonneg (by simp [Int.add_nonneg_of_nonneg_of_nonneg (Int.mul_nonneg_of_nonneg_of_nonneg (by norm_num) (Int.coe_nat_nonneg m)) (by norm_num)])] at this
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_two, Int.natCast_one] at this
    rw [← this]
    simp [Nat.add_mod, Nat.mul_mod]
  · intro h
    use Int.ofNat (n / 2)
    simp [Int.ofNat_add, Int.ofNat_mul]
    have : n = 2 * (n / 2) + 1 := by
      rw [← Nat.two_mul_div_two_add_one_of_odd]
      rw [Nat.odd_iff_not_even, Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      simp [h]
    rw [← Int.coe_nat_add, ← Int.coe_nat_mul, ← this]

-- LLM HELPER
lemma digit_last_even_iff (n : Nat) : n > 0 → (Even (Int.ofNat n) ↔ n % 10 % 2 = 0) := by
  intro h_pos
  rw [even_iff_mod_two_zero]
  constructor
  · intro h
    have : n % 2 = (n % 10) % 2 := by
      rw [← Nat.mod_mod_of_dvd]
      norm_num
    rw [← this]
    exact h
  · intro h
    have : n % 2 = (n % 10) % 2 := by
      rw [← Nat.mod_mod_of_dvd]
      norm_num
    rw [this]
    exact h

-- LLM HELPER
lemma digit_last_odd_iff (n : Nat) : n > 0 → (Odd (Int.ofNat n) ↔ n % 10 % 2 = 1) := by
  intro h_pos
  rw [odd_iff_mod_two_one]
  constructor
  · intro h
    have : n % 2 = (n % 10) % 2 := by
      rw [← Nat.mod_mod_of_dvd]
      norm_num
    rw [← this]
    exact h
  · intro h
    have : n % 2 = (n % 10) % 2 := by
      rw [← Nat.mod_mod_of_dvd]
      norm_num
    rw [this]
    exact h

-- LLM HELPER
lemma count_even_odd_digits_correct (n : Nat) : 
  let (even_count, odd_count) := count_even_odd_digits n
  (n = 0 → even_count = 1 ∧ odd_count = 0) ∧
  (n > 0 → 
    let last_digit := n % 10
    let rest := n / 10
    let (even_rest, odd_rest) := count_even_odd_digits rest
    (last_digit % 2 = 0 → even_count = even_rest + 1 ∧ odd_count = odd_rest) ∧
    (last_digit % 2 = 1 → even_count = even_rest ∧ odd_count = odd_rest + 1)) := by
  simp [count_even_odd_digits]
  by_cases h : n = 0
  · simp [h]
  · simp [h]
    have h_pos : n > 0 := Nat.pos_of_ne_zero h
    simp [count_even_odd_digits.aux]
    split_ifs
    · simp
    · simp

theorem correctness
(num: Int)
: problem_spec implementation num := by
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
        have : n = Int.natAbs num := rfl
        by_cases h : n = 0
        · simp [h, count_even_odd_digits, Even, Odd]
          constructor
          · constructor
            · intro h_even
              exfalso
              have : ¬Even (Int.ofNat 0) := by simp [Even]
              exact h_even ⟨0, by norm_num⟩
            · intro h_eq
              simp at h_eq
          · constructor
            · intro h_odd
              exfalso
              have : ¬Odd (Int.ofNat 0) := by simp [Odd]
              exact h_odd ⟨0, by norm_num⟩
            · intro h_eq
              simp at h_eq
              use 0
              norm_num
        · have h_pos : n > 0 := Nat.pos_of_ne_zero h
          simp [count_even_odd_digits, h]
          let last_digit := n % 10
          let rest := n / 10
          let (even_rest, odd_rest) := count_even_odd_digits rest
          constructor
          · rw [digit_last_even_iff n h_pos]
            by_cases h_even : last_digit % 2 = 0
            · simp [h_even]
            · simp [h_even]
              have h_odd : last_digit % 2 = 1 := by
                have : last_digit % 2 < 2 := Nat.mod_lt last_digit (by norm_num)
                omega
              simp [h_odd]
          · rw [digit_last_odd_iff n h_pos]
            by_cases h_even : last_digit % 2 = 0
            · simp [h_even]
            · simp [h_even]
              have h_odd : last_digit % 2 = 1 := by
                have : last_digit % 2 < 2 := Nat.mod_lt last_digit (by norm_num)
                omega
              simp [h_odd]
      · intro h_nonneg
        have : n = Int.natAbs num := rfl
        by_cases h : n = 0
        · simp [h, count_even_odd_digits, Even, Odd]
          constructor
          · constructor
            · intro h_odd
              exfalso
              have : ¬Odd (Int.ofNat 0) := by simp [Odd]
              exact h_odd ⟨0, by norm_num⟩
            · intro h_eq
              simp at h_eq
          · constructor
            · intro h_even
              exfalso
              have : ¬Even (Int.ofNat 0) := by simp [Even]
              exact h_even ⟨0, by norm_num⟩
            · intro h_eq
              simp at h_eq
              use 0
              norm_num
        · have h_pos : n > 0 := Nat.pos_of_ne_zero h
          simp [count_even_odd_digits, h]
          let last_digit := n % 10
          let rest := n / 10
          let (even_rest, odd_rest) := count_even_odd_digits rest
          constructor
          · rw [digit_last_odd_iff n h_pos]
            by_cases h_even : last_digit % 2 = 0
            · simp [h_even]
            · simp [h_even]
              have h_odd : last_digit % 2 = 1 := by
                have : last_digit % 2 < 2 := Nat.mod_lt last_digit (by norm_num)
                omega
              simp [h_odd]
          · rw [digit_last_even_iff n h_pos]
            by_cases h_even : last_digit % 2 = 0
            · simp [h_even]
            · simp [h_even]
              have h_odd : last_digit % 2 = 1 := by
                have : last_digit % 2 < 2 := Nat.mod_lt last_digit (by norm_num)
                omega
              simp [h_odd]