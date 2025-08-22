import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := |num|.toNat;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl numBy10;
  (result = impl numAbs) ∧
  (0 ≤ num → (Even num ↔ 1 + even_count' = even_count) ∧ (Odd num ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd num ↔ 1 + odd_count' = odd_count) ∧ (Even num ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def count_even_odd_digits (n : Nat) : Nat × Nat :=
  if n = 0 then (1, 0)
  else
    let digit := n % 10
    let (even_rest, odd_rest) := count_even_odd_digits (n / 10)
    if digit % 2 = 0 then (even_rest + 1, odd_rest)
    else (even_rest, odd_rest + 1)

def implementation (num: Int) : Int × Int := 
  let n := |num|.toNat
  let (even_count, odd_count) := count_even_odd_digits n
  (Int.ofNat even_count, Int.ofNat odd_count)

-- LLM HELPER
lemma count_even_odd_digits_base (n : Nat) :
  n = 0 → count_even_odd_digits n = (1, 0) := by
  intro h
  rw [count_even_odd_digits, h, if_pos rfl]

-- LLM HELPER
lemma count_even_odd_digits_pos (n : Nat) :
  n > 0 → 
  let digit := n % 10
  let (even_rest, odd_rest) := count_even_odd_digits (n / 10)
  count_even_odd_digits n = 
    if digit % 2 = 0 then (even_rest + 1, odd_rest)
    else (even_rest, odd_rest + 1) := by
  intro h
  rw [count_even_odd_digits]
  rw [if_neg (ne_of_gt h)]
  rfl

-- LLM HELPER
lemma implementation_def (num : Int) :
  implementation num = (Int.ofNat (count_even_odd_digits |num|.toNat).1, Int.ofNat (count_even_odd_digits |num|.toNat).2) := by
  rw [implementation]
  simp only [Prod.mk.eta]

-- LLM HELPER
lemma toNat_div_ten_eq (n : Nat) :
  |Int.ofNat (n / 10)|.toNat = n / 10 := by
  simp only [Int.natAbs_of_nonneg (Int.ofNat_nonneg _), Int.toNat_of_nonneg (Int.ofNat_nonneg _)]

-- LLM HELPER
lemma count_even_odd_digits_even (n : Nat) (h : n > 0) :
  let digit := n % 10
  Even (Int.ofNat digit) ↔ 
  (count_even_odd_digits n).1 = (count_even_odd_digits (n / 10)).1 + 1 := by
  rw [count_even_odd_digits_pos n h]
  simp only [Int.even_iff_two_dvd, Int.ofNat_mod]
  cases' Nat.mod_two_eq_zero_or_one digit with h_even h_odd
  · simp only [h_even, Int.ofNat_zero, dvd_zero, true_iff]
    rw [if_pos h_even]
    simp only [Prod.fst_mk, Prod.snd_mk]
    rfl
  · simp only [h_odd, Int.ofNat_one, Int.one_emod_two_eq_one, false_iff]
    rw [if_neg (Nat.one_ne_zero ∘ h_odd ▸ ·)]
    simp only [Prod.fst_mk, Prod.snd_mk]
    linarith

theorem correctness
(num: Int)
: problem_spec implementation num := by
  rw [problem_spec]
  use implementation num
  constructor
  · rfl
  · constructor
    · simp only [implementation_def]
      simp only [Int.natAbs_div_natAbs]
      rw [Int.toNat_of_nonneg (Int.natAbs_nonneg num)]
      rw [Int.toNat_of_nonneg (Int.natAbs_nonneg num)]
      simp only [Int.natAbs_of_nonneg (Int.natAbs_nonneg num)]
      simp only [Int.natAbs_natAbs]
      rfl
    · constructor
      · intro h
        constructor
        · constructor
          · intro h_even
            simp only [implementation_def]
            simp only [Int.natAbs_div_natAbs]
            rw [Int.toNat_of_nonneg h]
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)]
            simp only [Int.natAbs_of_nonneg h]
            simp only [Int.natAbs_natAbs]
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rfl
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rw [Int.toNat_of_nonneg h] at h_even
              simp only [Int.even_iff_two_dvd] at h_even
              have digit_even : (num.toNat % 10) % 2 = 0 := by
                rw [← Int.natAbs_mod, Int.natAbs_of_nonneg h, Int.toNat_of_nonneg h] at h_even
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg (Int.ofNat_nonneg _)] at h_even
                exact Nat.mod_two_eq_zero_iff_even.mpr (Int.even_iff_two_dvd.mp h_even)
              rw [if_pos digit_even]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rfl
          · intro h_eq
            simp only [implementation_def] at h_eq
            simp only [Int.natAbs_div_natAbs] at h_eq
            rw [Int.toNat_of_nonneg h] at h_eq
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)] at h_eq
            simp only [Int.natAbs_of_nonneg h] at h_eq
            simp only [Int.natAbs_natAbs] at h_eq
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h] at h_eq
              simp only [h_zero, Int.ofNat_zero] at h_eq
              simp only [Int.zero_mod, Int.even_zero]
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h]
              simp only [Int.even_iff_two_dvd]
              by_cases digit_even : (num.toNat % 10) % 2 = 0
              · rw [if_pos digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg h]
                rw [Int.toNat_of_nonneg h]
                exact Nat.even_iff_two_dvd.mp (Nat.mod_two_eq_zero_iff_even.mpr digit_even)
              · rw [if_neg digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                exfalso
                linarith
        · constructor
          · intro h_odd
            simp only [implementation_def]
            simp only [Int.natAbs_div_natAbs]
            rw [Int.toNat_of_nonneg h]
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)]
            simp only [Int.natAbs_of_nonneg h]
            simp only [Int.natAbs_natAbs]
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rw [Int.toNat_of_nonneg h] at h_odd
              simp only [h_zero, Int.ofNat_zero, Int.odd_zero] at h_odd
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rw [Int.toNat_of_nonneg h] at h_odd
              simp only [Int.odd_iff_not_even] at h_odd
              have digit_odd : (num.toNat % 10) % 2 ≠ 0 := by
                rw [← Int.natAbs_mod, Int.natAbs_of_nonneg h, Int.toNat_of_nonneg h] at h_odd
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg (Int.ofNat_nonneg _)] at h_odd
                rw [← Nat.mod_two_eq_zero_iff_even]
                exact Int.not_even_iff_odd.mp h_odd
              rw [if_neg digit_odd]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rfl
          · intro h_eq
            simp only [implementation_def] at h_eq
            simp only [Int.natAbs_div_natAbs] at h_eq
            rw [Int.toNat_of_nonneg h] at h_eq
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)] at h_eq
            simp only [Int.natAbs_of_nonneg h] at h_eq
            simp only [Int.natAbs_natAbs] at h_eq
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h] at h_eq
              simp only [h_zero, Int.ofNat_zero] at h_eq
              simp only [Int.zero_mod, Int.odd_zero]
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h]
              simp only [Int.odd_iff_not_even]
              by_cases digit_even : (num.toNat % 10) % 2 = 0
              · rw [if_pos digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                exfalso
                linarith
              · rw [if_neg digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg h]
                rw [Int.toNat_of_nonneg h]
                rw [← Nat.mod_two_eq_zero_iff_even]
                exact digit_even
      · intro h
        constructor
        · constructor
          · intro h_odd
            simp only [implementation_def]
            simp only [Int.natAbs_div_natAbs]
            rw [Int.toNat_of_nonneg h]
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)]
            simp only [Int.natAbs_of_nonneg h]
            simp only [Int.natAbs_natAbs]
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rw [Int.toNat_of_nonneg h] at h_odd
              simp only [h_zero, Int.ofNat_zero, Int.odd_zero] at h_odd
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rw [Int.toNat_of_nonneg h] at h_odd
              simp only [Int.odd_iff_not_even] at h_odd
              have digit_odd : (num.toNat % 10) % 2 ≠ 0 := by
                rw [← Int.natAbs_mod, Int.natAbs_of_nonneg h, Int.toNat_of_nonneg h] at h_odd
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg (Int.ofNat_nonneg _)] at h_odd
                rw [← Nat.mod_two_eq_zero_iff_even]
                exact Int.not_even_iff_odd.mp h_odd
              rw [if_neg digit_odd]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rfl
          · intro h_eq
            simp only [implementation_def] at h_eq
            simp only [Int.natAbs_div_natAbs] at h_eq
            rw [Int.toNat_of_nonneg h] at h_eq
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)] at h_eq
            simp only [Int.natAbs_of_nonneg h] at h_eq
            simp only [Int.natAbs_natAbs] at h_eq
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h] at h_eq
              simp only [h_zero, Int.ofNat_zero] at h_eq
              simp only [Int.zero_mod, Int.odd_zero]
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h]
              simp only [Int.odd_iff_not_even]
              by_cases digit_even : (num.toNat % 10) % 2 = 0
              · rw [if_pos digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                exfalso
                linarith
              · rw [if_neg digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg h]
                rw [Int.toNat_of_nonneg h]
                rw [← Nat.mod_two_eq_zero_iff_even]
                exact digit_even
        · constructor
          · intro h_even
            simp only [implementation_def]
            simp only [Int.natAbs_div_natAbs]
            rw [Int.toNat_of_nonneg h]
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)]
            simp only [Int.natAbs_of_nonneg h]
            simp only [Int.natAbs_natAbs]
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rfl
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rw [Int.toNat_of_nonneg h] at h_even
              simp only [Int.even_iff_two_dvd] at h_even
              have digit_even : (num.toNat % 10) % 2 = 0 := by
                rw [← Int.natAbs_mod, Int.natAbs_of_nonneg h, Int.toNat_of_nonneg h] at h_even
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg (Int.ofNat_nonneg _)] at h_even
                exact Nat.mod_two_eq_zero_iff_even.mpr (Int.even_iff_two_dvd.mp h_even)
              rw [if_pos digit_even]
              simp only [Prod.fst_mk, Prod.snd_mk]
              rfl
          · intro h_eq
            simp only [implementation_def] at h_eq
            simp only [Int.natAbs_div_natAbs] at h_eq
            rw [Int.toNat_of_nonneg h] at h_eq
            rw [Int.toNat_of_nonneg (Int.natAbs_nonneg _)] at h_eq
            simp only [Int.natAbs_of_nonneg h] at h_eq
            simp only [Int.natAbs_natAbs] at h_eq
            by_cases h_zero : num.toNat = 0
            · simp only [h_zero, count_even_odd_digits_base, Nat.zero_div] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h] at h_eq
              simp only [h_zero, Int.ofNat_zero] at h_eq
              simp only [Int.zero_mod, Int.even_zero]
            · have h_pos : num.toNat > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos num.toNat h_pos] at h_eq
              simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
              rw [Int.toNat_of_nonneg h]
              simp only [Int.even_iff_two_dvd]
              by_cases digit_even : (num.toNat % 10) % 2 = 0
              · rw [if_pos digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                exfalso
                linarith
              · rw [if_neg digit_even] at h_eq
                simp only [Prod.fst_mk, Prod.snd_mk] at h_eq
                simp only [Int.natAbs_mod, Int.natAbs_of_nonneg h]
                rw [Int.toNat_of_nonneg h]
                exact Nat.even_iff_two_dvd.mp (Nat.mod_two_eq_zero_iff_even.mpr digit_even)