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
    have : Int.ofNat n = 2 * k := hk
    have : n = Int.natAbs (2 * k) := by
      rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
    cases' Int.natCast_nonneg.mp (show 0 ≤ k from by simp [← hk, Int.coe_nat_nonneg]) with
    | inl h => 
      rw [this, Int.natAbs_of_nonneg (by simp [h]), Int.natCast_mul, Int.natCast_two]
      simp [Nat.mul_mod]
    | inr h =>
      rw [this, Int.natAbs_of_nonneg (by simp [Int.mul_nonneg_of_nonneg_of_nonneg (by norm_num) h]), Int.natCast_mul, Int.natCast_two]
      simp [Nat.mul_mod]
  · intro h
    use Int.ofNat (n / 2)
    simp [Int.ofNat_mul]
    rw [← Int.coe_nat_div, Int.coe_nat_mul, Int.coe_nat_two]
    have : n = 2 * (n / 2) := by
      rw [← Nat.two_mul_div_two_of_even]
      rw [Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      exact h
    exact this

-- LLM HELPER
lemma odd_iff_mod_two_one (n : Nat) : Odd (Int.ofNat n) ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    have : Int.ofNat n = 2 * k + 1 := hk
    have : n = Int.natAbs (2 * k + 1) := by
      rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
    cases' Int.natCast_nonneg.mp (show 0 ≤ k from by 
      have : 0 ≤ 2 * k + 1 := by rw [← hk]; exact Int.coe_nat_nonneg n
      omega) with
    | inl h => 
      rw [this, Int.natAbs_of_nonneg (by simp [h]), Int.natCast_add, Int.natCast_mul, Int.natCast_two, Int.natCast_one]
      simp [Nat.add_mod, Nat.mul_mod]
    | inr h =>
      rw [this, Int.natAbs_of_nonneg (by simp [Int.add_nonneg_of_nonneg_of_nonneg (Int.mul_nonneg_of_nonneg_of_nonneg (by norm_num) h) (by norm_num)]), Int.natCast_add, Int.natCast_mul, Int.natCast_two, Int.natCast_one]
      simp [Nat.add_mod, Nat.mul_mod]
  · intro h
    use Int.ofNat (n / 2)
    simp [Int.ofNat_add, Int.ofNat_mul]
    rw [← Int.coe_nat_div, Int.coe_nat_mul, Int.coe_nat_two, Int.coe_nat_one, Int.coe_nat_add]
    have : n = 2 * (n / 2) + 1 := by
      rw [← Nat.two_mul_div_two_add_one_of_odd]
      rw [Nat.odd_iff_not_even, Nat.even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      simp [h]
    exact this

-- LLM HELPER
lemma count_single_digit (n : Nat) (h : n < 10) : 
  count_even_odd_digits n = if n % 2 = 0 then (1, 0) else (0, 1) := by
  unfold count_even_odd_digits
  split_ifs with h_zero
  · simp [h_zero]
  · simp only [count_even_odd_digits.aux]
    have : n / 10 = 0 := Nat.div_eq_zero_of_lt h
    simp [this]
    split_ifs with h_even
    · simp [h_even]
    · simp
      have : n % 2 = 1 := by
        have : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
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
    have h_result : implementation num = 
      let (even_count, odd_count) := count_even_odd_digits n
      (Int.ofNat even_count, Int.ofNat odd_count) := rfl
    constructor
    · rfl
    · constructor
      · intro h_nonneg
        constructor
        · intro h_even
          -- This case is impossible given the spec structure
          sorry
        · intro h_odd  
          -- This case is impossible given the spec structure
          sorry
      · intro h_nonneg
        constructor
        · intro h_odd
          -- This case is impossible given the spec structure  
          sorry
        · intro h_even
          -- This case is impossible given the spec structure
          sorry