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
lemma nat_even_iff_int_even (n : Nat) : Even (Int.ofNat n) ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    rw [Int.ofNat_eq_coe] at hk
    have : (n : Int) = 2 * k := hk
    have : n = Int.natAbs (2 * k) := by
      rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
    rw [this]
    cases' Int.natAbs_eq k with h h
    · rw [h, Int.natAbs_mul, Int.natAbs_two]
      simp [Nat.mul_mod]
    · rw [h, Int.natAbs_mul, Int.natAbs_two]
      simp [Nat.mul_mod]
  · intro h
    use (n / 2 : Int)
    rw [Int.ofNat_eq_coe]
    have : n = 2 * (n / 2) := by
      rw [← Nat.two_mul_div_two_of_even]
      rw [Nat.even_iff_two_dvd]
      exact Nat.dvd_iff_mod_eq_zero.mpr h
    rw [this]
    simp [Int.coe_nat_mul]

-- LLM HELPER
lemma nat_odd_iff_int_odd (n : Nat) : Odd (Int.ofNat n) ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    rw [Int.ofNat_eq_coe] at hk
    have : (n : Int) = 2 * k + 1 := hk
    have : n = Int.natAbs (2 * k + 1) := by
      rw [← hk, Int.natAbs_of_nonneg (Int.coe_nat_nonneg n)]
    rw [this]
    cases' Int.natAbs_eq k with h h
    · rw [h, Int.natAbs_add_one, Int.natAbs_mul, Int.natAbs_two]
      simp [Nat.add_mod, Nat.mul_mod]
    · rw [h, Int.natAbs_add_one, Int.natAbs_mul, Int.natAbs_two]
      simp [Nat.add_mod, Nat.mul_mod]
  · intro h
    use ((n - 1) / 2 : Int)
    rw [Int.ofNat_eq_coe]
    have : n = 2 * ((n - 1) / 2) + 1 := by
      have : n ≥ 1 := by
        by_contra h_not
        simp at h_not
        interval_cases n
        · simp at h
        · simp at h
      rw [← Nat.two_mul_div_two_add_one_of_odd]
      rw [Nat.odd_iff_not_even, Nat.even_iff_two_dvd]
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [h]
    rw [this]
    simp [Int.coe_nat_add, Int.coe_nat_mul]

theorem correctness
(num: Int)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h
    unfold implementation
    simp only [Int.natAbs_of_nonneg h]
    let n := Int.natAbs num
    have n_eq : n = Int.natAbs num := rfl
    constructor
    · constructor
      · intro h_even
        rw [nat_even_iff_int_even] at h_even
        sorry
      · intro h_odd  
        rw [nat_odd_iff_int_odd] at h_odd
        sorry
    · constructor
      · intro h_odd
        rw [nat_odd_iff_int_odd] at h_odd
        sorry
      · intro h_even
        rw [nat_even_iff_int_even] at h_even
        sorry