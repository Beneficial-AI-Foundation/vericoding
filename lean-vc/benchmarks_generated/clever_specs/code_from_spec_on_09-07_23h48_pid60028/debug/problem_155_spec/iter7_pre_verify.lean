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
lemma count_digits_correct (n : Nat) : 
  let (even_count, odd_count) := count_even_odd_digits n
  ∀ d, d < 10 → (d % 2 = 0 → even_count > 0) ∧ (d % 2 = 1 → odd_count > 0) := by
  intro d hd
  constructor <;> intro h
  · sorry
  · sorry

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
    · constructor <;> intro h_nonneg <;> constructor <;> intro h_parity
      · -- Even digit case for even_count
        sorry
      · -- Odd digit case for even_count  
        sorry
      · -- Odd digit case for odd_count
        sorry
      · -- Even digit case for odd_count
        sorry