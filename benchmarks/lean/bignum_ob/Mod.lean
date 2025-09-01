import Mathlib
import BigNum.Defs
import BigNum.Convert

/-! # Correctness of mod related definitions.

Main results:

* Proof that the binary definition of a number with a power of two corresponds to a power of two
    `isPowTwo_iff`: `isPowTwo bs ↔ (0 < listBoolToNat bs ∧ ∃ k, listBoolToNat bs = 2^k)`
* Proof that the bignum definition of mod to a power of two is correct (variant 1)
  `modPowTwoListBool_listBoolToNat`:
    `listBoolToNat (modPowTwoListBool as bs) = (listBoolToNat as) % (listBoolToNat bs)`
* Proof that the bignum definition of mod to a power of two is correct (variant 2)
    `modPowTwo_correct`: `strToNat (modPowTwo a b) = strToNat a % strToNat b`
* Proof that the bignum definition of mod to a power of two is correct (variant 3)
    `modPowTwo_correct'`: `strToNat (modPowTwo (natToStr m) (natToStr (2 ^ n))) = m % (2 ^ n)`
-/

@[simp]
lemma isZero_of_empty : isZero [] := by
  sorry

@[simp]
lemma isOne_of_true : isOne [true] := by
  sorry

@[simp]
lemma listBoolToNat_of_isZero (bs : List Bool) : isZero bs ↔ listBoolToNat bs = 0 := by
  sorry

@[simp]
lemma listBoolToNat_of_isOne (bs : List Bool) : isOne bs ↔ listBoolToNat bs = 1 := by
  sorry

lemma isZero_tail {tail : List Bool} (h : ∃ k, listBoolToNat (true :: tail) = 2 ^ k) :
    isZero tail := by
  sorry

lemma isPowTwo_of_isPowTwo_tail {tail} (h : isPowTwo tail) : isPowTwo (false :: tail) := by
  sorry

theorem isPowTwo_iff (bs : List Bool) :
    isPowTwo bs ↔ (0 < listBoolToNat bs ∧ ∃ k, listBoolToNat bs = 2^k) := by
  sorry

@[simp]
lemma modPowTwoListBool_of_empty {as : List Bool} : modPowTwoListBool as [] = as := by
  sorry

@[simp]
lemma modPowTwoListBool_of_true {as bs} : modPowTwoListBool as (true :: bs) = [] := by
  sorry

@[simp]
lemma isPowTwo_of_isPowTwo {tail} (h : isPowTwo (false :: tail)) : isPowTwo (tail) := by
  sorry

@[simp]
lemma isZero_of_isPowTwo {tail} (h : isPowTwo (true :: tail)) : isZero tail := by
  sorry

-- Surprising that this isn't already available or easier to prove
/-- If `Even a` and `Even b` then `a < b` implies that `a + 2 ≤ b`. -/
lemma add_two_le_of_even_of_lt (a b : Nat) (ha : Even a) (hb : Even b) (h : a < b) : a + 2 ≤ b := by
  sorry

/-- Unexpected effect of natural number division for even numbers. -/
lemma div_even_add_one (A B : Nat) : 2 * A / (2 * B) = (2 * A + 1) / (2 * B) := by
  sorry

-- Surprising that this isn't easier to prove, requires the above two lemmas in current formulation.
lemma simple_yet_seemingly_hard (A B : Nat) : 2 * (A % B) + 1 = (2 * A + 1) % (2 * B) := by
  sorry

lemma modPowTwoListBool_listBoolToNat (as bs : List Bool) (h : isPowTwo bs) :
    listBoolToNat (modPowTwoListBool as bs) = (listBoolToNat as) % (listBoolToNat bs) := by
  sorry

/-- BigNum modPowTwo coincides with `Nat` addition. -/
theorem modPowTwo_correct (a b : String) (h : isPowTwo' b) :
    strToNat (modPowTwo a b) = strToNat a % strToNat b := by
  sorry

/-- BigNum modPowTwo coincides with `Nat` addition. -/
theorem modPowTwo_correct' (m n : Nat) :
    strToNat (modPowTwo (natToStr m) (natToStr (2 ^ n))) = m % (2 ^ n) := by
  sorry
