/- 
function_signature: "def is_equal_to_sum_even(n: int) -> Bool"
docstring: |
    Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
test_cases:
  - input: 4
    expected_output: False
  - input: 6
    expected_output: False
  - input: 8
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Int) : Bool :=
  n >= 8 && n % 2 = 0

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
    0 < a ∧
    0 < b ∧
    0 < c ∧
    0 < d ∧
    (a + b + c + d = n);
  result = true ↔ sum_exists
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma nat_even_pos_ge_two (a : Nat) (ha_even : Even a) (ha_pos : 0 < a) : 2 ≤ a := by
  obtain ⟨k, hk⟩ := ha_even
  rw [hk] at ha_pos
  have : 0 < k := by
    by_contra h
    push_neg at h
    interval_cases k
    simp at ha_pos
  omega

-- LLM HELPER
lemma sum_four_pos_evens_ge_eight (a b c d : Nat) 
  (ha_even : Even a) (hb_even : Even b) (hc_even : Even c) (hd_even : Even d)
  (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c) (hd_pos : 0 < d) :
  8 ≤ a + b + c + d := by
  have ha_ge : 2 ≤ a := nat_even_pos_ge_two a ha_even ha_pos
  have hb_ge : 2 ≤ b := nat_even_pos_ge_two b hb_even hb_pos
  have hc_ge : 2 ≤ c := nat_even_pos_ge_two c hc_even hc_pos
  have hd_ge : 2 ≤ d := nat_even_pos_ge_two d hd_even hd_pos
  omega

-- LLM HELPER
lemma sum_four_evens_even (a b c d : Nat) 
  (ha_even : Even a) (hb_even : Even b) (hc_even : Even c) (hd_even : Even d) :
  Even (a + b + c + d) := by
  have h1 : Even (a + b) := Even.add ha_even hb_even
  have h2 : Even (c + d) := Even.add hc_even hd_even
  rw [← add_assoc, ← add_assoc]
  rw [add_assoc a b (c + d)]
  exact Even.add h1 h2

-- LLM HELPER
lemma construct_sum_for_valid_n (n : Int) (hn_ge : 8 ≤ n) (hn_even : Even n) :
  ∃ a b c d : Nat, Even a ∧ Even b ∧ Even c ∧ Even d ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ (a + b + c + d = n) := by
  have hn_nat : ↑n.natAbs = n := by
    rw [Int.natAbs_of_nonneg]
    omega
  have hn_nat_ge : 8 ≤ n.natAbs := by
    rw [← Int.natCast_natAbs]
    rw [Int.natAbs_of_nonneg]
    exact hn_ge
    omega
  have hn_nat_even : Even n.natAbs := by
    rw [← Int.natCast_even, hn_nat]
    exact hn_even
  
  obtain ⟨k, hk⟩ := hn_nat_even
  have hk_corrected : n.natAbs = 2 * k := by
    rw [hk, two_mul]
  have hk_ge : 4 ≤ k := by
    have : n.natAbs = 2 * k := hk_corrected
    rw [this] at hn_nat_ge
    omega
  
  use 2, 2, 2, 2 * (k - 3)
  constructor; exact ⟨1, rfl⟩
  constructor; exact ⟨1, rfl⟩
  constructor; exact ⟨1, rfl⟩
  constructor
  · use k - 3
    ring
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor
  · omega
  · rw [← hn_nat, hk_corrected]
    simp only [Nat.cast_mul]
    ring_nf
    ring

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use (n >= 8 && n % 2 = 0)
  constructor
  · rfl
  · constructor
    · intro h
      rw [Bool.and_eq_true] at h
      obtain ⟨hn_ge, hn_mod⟩ := h
      have hn_even : Even n := by
        rw [Int.even_iff_two_dvd]
        rw [dvd_iff_emod_eq_zero]
        exact Int.decide_eq_true_iff.mp hn_mod
      obtain ⟨a, b, c, d, ha_even, hb_even, hc_even, hd_even, ha_pos, hb_pos, hc_pos, hd_pos, hsum⟩ := 
        construct_sum_for_valid_n n (Int.decide_eq_true_iff.mp hn_ge) hn_even
      use a, b, c, d
      exact ⟨ha_even, hb_even, hc_even, hd_even, ha_pos, hb_pos, hc_pos, hd_pos, hsum⟩
    · intro h
      obtain ⟨a, b, c, d, ha_even, hb_even, hc_even, hd_even, ha_pos, hb_pos, hc_pos, hd_pos, hsum⟩ := h
      rw [Bool.and_eq_true]
      constructor
      · have : 8 ≤ a + b + c + d := sum_four_pos_evens_ge_eight a b c d ha_even hb_even hc_even hd_even ha_pos hb_pos hc_pos hd_pos
        have : (8 : Int) ≤ ↑(a + b + c + d) := by
          rw [← Int.natCast_le]
          exact this
        rw [hsum] at this
        exact Int.decide_eq_true_iff.mpr this
      · have : Even (a + b + c + d) := sum_four_evens_even a b c d ha_even hb_even hc_even hd_even
        have : Even (↑(a + b + c + d) : Int) := by
          rw [Int.natCast_even]
          exact this
        rw [hsum] at this
        rw [Int.even_iff_two_dvd] at this
        rw [dvd_iff_emod_eq_zero] at this
        exact Int.decide_eq_true_iff.mpr this

-- #test implementation 4 = false
-- #test implementation 6 = false
-- #test implementation 8 = true