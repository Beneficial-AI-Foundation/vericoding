import Mathlib
import BigNum.Defs
import BigNum.Add
import BigNum.Convert

/-! # Correctness of multiplication.

Multiplication of BigNums corresponds to multiplication of the natural numbers.

Main results:

* `mul_correct`: `strToNat (mul a b) = strToNat a * strToNat b`;
* `mul_correct'`: `strToNat (mul (natToStr m) (natToStr n)) = m * n`;
* `mulListBool_correct`: `listBoolToNat (mulListBool a b) = listBoolToNat a * listBoolToNat b`.

-/

/-! ## multiplication of List Bool -/

@[simp]
lemma shiftLeft_of_empty : shiftLeft [] = [] :=
  sorry

@[simp]
lemma shiftLeft_listBoolToNat (bs : List Bool) :
    listBoolToNat (shiftLeft bs) = 2 * listBoolToNat bs := by
  sorry

@[simp]
lemma mulListBool_aux_of_empty_right a acc : mulListBool_aux a [] acc = acc :=
  sorry

@[simp]
lemma mulListBool_aux_of_empty_left b acc : mulListBool_aux [] b acc = acc := by
  sorry

@[simp]
lemma mulListBool_listBoolToNat_right a acc : listBoolToNat (mulListBool_aux a [true] acc) =
    listBoolToNat a + listBoolToNat acc := by
  sorry

-- Correctness theorem for mulListBool_aux
@[simp]
theorem mulListBool_aux_listBoolToNat a b acc:
    listBoolToNat (mulListBool_aux a b acc) =
    listBoolToNat acc + listBoolToNat a * listBoolToNat b := by
  sorry

theorem mulListBool_correct (a b : List Bool) :
    listBoolToNat (mulListBool a b) = listBoolToNat a * listBoolToNat b := by
  sorry

/-! ## multiplication of BigNum strings -/

/-- BigNum multiplication agrees with `Nat` multiplication. -/
@[simp]
theorem mul_correct (a b : String) : strToNat (mul a b) = strToNat a * strToNat b := by
  sorry

/-- BigNum multiplication agrees with `Nat` multiplication. -/
theorem mul_correct' (m n : Nat) : strToNat (mul (natToStr m) (natToStr n)) = m * n := by
  sorry
