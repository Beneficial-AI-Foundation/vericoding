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
lemma shiftLeft_of_empty : shiftLeft [] = [] := rfl

@[simp]
lemma shiftLeft_listBoolToNat (bs : List Bool) :
    listBoolToNat (shiftLeft bs) = 2 * listBoolToNat bs := by
  induction bs with
  | nil => simp
  | cons h t ih => simp [shiftLeft]

@[simp]
lemma mulListBool_aux_of_empty_right a acc : mulListBool_aux a [] acc = acc := rfl

@[simp]
lemma mulListBool_aux_of_empty_left b acc : mulListBool_aux [] b acc = acc := by
  induction b with
  | nil => simp
  | cons head tail ih =>
    unfold mulListBool_aux
    obtain hc | hc := Bool.eq_false_or_eq_true head
    all_goals
    · simp [hc, ih]

@[simp]
lemma mulListBool_listBoolToNat_right a acc : listBoolToNat (mulListBool_aux a [true] acc) =
    listBoolToNat a + listBoolToNat acc := by
  unfold mulListBool_aux
  simp [addListBool_listBoolToNat acc a false, add_comm]

-- Correctness theorem for mulListBool_aux
@[simp]
theorem mulListBool_aux_listBoolToNat a b acc:
    listBoolToNat (mulListBool_aux a b acc) =
      listBoolToNat acc + listBoolToNat a * listBoolToNat b := by
  induction b generalizing a acc with
  | nil =>
    simp [mulListBool_aux, listBoolToNat]
  | cons hb tb ih =>
    cases hb with
    | false =>
      simp [mulListBool_aux, ih]
      ring
    | true =>
      simp [mulListBool_aux, ih, addListBool_listBoolToNat]
      ring

theorem mulListBool_correct (a b : List Bool) :
    listBoolToNat (mulListBool a b) = listBoolToNat a * listBoolToNat b := by
  simp [mulListBool]

/-! ## multiplication of BigNum strings -/

/-- BigNum multiplication agrees with `Nat` multiplication. -/
@[simp]
theorem mul_correct (a b : String) : strToNat (mul a b) = strToNat a * strToNat b := by
  unfold mul
  simpa using mulListBool_correct (strToListBool a) (strToListBool b)

/-- BigNum multiplication agrees with `Nat` multiplication. -/
theorem mul_correct' (m n : Nat) : strToNat (mul (natToStr m) (natToStr n)) = m * n := by
  simp [mul_correct]
