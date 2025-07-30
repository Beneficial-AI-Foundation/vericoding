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
lemma digit_even_iff (n : Nat) : Even (Int.ofNat n) ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    cases' Int.natAbs_eq k with h h
    · have : n = Int.natAbs (2 * k) := by
        rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
      rw [this, h, Int.natAbs_mul, Int.natAbs_two]
      simp [Nat.mul_mod]
    · have : n = Int.natAbs (2 * k) := by
        rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
      rw [this, h, Int.natAbs_mul, Int.natAbs_two]
      simp [Nat.mul_mod]
  · intro h
    use (n / 2 : Int)
    simp [Int.ofNat_mul, Nat.two_mul_div_two_of_even]
    rw [Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    exact h

-- LLM HELPER
lemma digit_odd_iff (n : Nat) : Odd (Int.ofNat n) ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    cases' Int.natAbs_eq k with h h
    · have : n = Int.natAbs (2 * k + 1) := by
        rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
      rw [this]
      cases' k with k_pos k_neg
      · simp [Int.natAbs_add_nonneg, Int.natAbs_mul, Int.natAbs_two]
        simp [Nat.add_mod, Nat.mul_mod]
      · simp [Int.natAbs_add_nonneg, Int.natAbs_mul, Int.natAbs_two]
        simp [Nat.add_mod, Nat.mul_mod]
    · have : n = Int.natAbs (2 * k + 1) := by
        rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
      rw [this]
      cases' k with k_pos k_neg
      · simp [Int.natAbs_add_nonneg, Int.natAbs_mul, Int.natAbs_two]
        simp [Nat.add_mod, Nat.mul_mod]
      · simp [Int.natAbs_add_nonneg, Int.natAbs_mul, Int.natAbs_two]
        simp [Nat.add_mod, Nat.mul_mod]
  · intro h
    use ((n - 1) / 2 : Int)
    simp [Int.ofNat_add, Int.ofNat_mul]
    have : n = 2 * ((n - 1) / 2) + 1 := by
      rw [← Nat.two_mul_div_two_add_one_of_odd]
      rw [Nat.odd_iff_not_even, Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      simp [h]
    exact this

-- LLM HELPER
lemma count_even_odd_correct (n : Nat) :
  let (even_count, odd_count) := count_even_odd_digits n
  (n = 0 → even_count = 1 ∧ odd_count = 0) ∧
  (n > 0 → 
    let last_digit := n % 10
    let rest := n / 10
    let (even_rest, odd_rest) := count_even_odd_digits rest
    (last_digit % 2 = 0 → even_count = even_rest + 1 ∧ odd_count = odd_rest) ∧
    (last_digit % 2 = 1 → even_count = even_rest ∧ odd_count = odd_rest + 1)) := by
  unfold count_even_odd_digits
  split_ifs with h
  · simp [h]
  · simp only [count_even_odd_digits.aux]
    constructor
    · intro h_zero
      simp [h_zero] at h
    · intro h_pos
      by_cases h2 : n % 10 % 2 = 0
      · simp [h2]
      · simp [h2]
        have : n % 10 % 2 = 1 := by
          have : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
          have : n % 10 % 2 < 2 := Nat.mod_lt _ (by norm_num)
          omega
        exact this

theorem correctness
(num: Int)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · unfold implementation
    simp only [Int.natAbs_of_nonneg]
    let n := Int.natAbs num
    constructor
    · rfl
    · constructor
      · intro h_nonneg
        constructor
        · intro h_even
          rw [digit_even_iff] at h_even
          simp
        · intro h_odd
          rw [digit_odd_iff] at h_odd
          simp
      · intro h_nonneg
        constructor
        · intro h_odd
          rw [digit_odd_iff] at h_odd
          simp
        · intro h_even
          rw [digit_even_iff] at h_even
          simp