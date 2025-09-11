import Mathlib
import BigNum.Defs
import BigNum.Convert

/-! # Correctness of addition.

Addition of BigNums corresponds to addition of the natural numbers.

Main results:

* `add_correct`: `strToNat (add a b) = strToNat a + strToNat b`;
* `add_correct'`: `strToNat (add (natToStr m) (natToStr n)) = m + n`;
* `addListBool_listBoolToNat`:
    `listBoolToNat (addListBool a b carry) = listBoolToNat a + listBoolToNat b `.
-/

/-! ## Addition of List Bool -/

@[simp]
lemma addBitsWithCarry_of_FXF (b : Bool) : addBitsWithCarry false b false = (b, false) := by
  sorry

@[simp]
lemma addBitsWithCarry_of_XFF (b : Bool) : addBitsWithCarry  b false false = (b, false) := by
  sorry

@[simp]
lemma addBitsWithCarry_of_FFT : addBitsWithCarry false false true = (true, false) := by
  sorry

@[simp]
lemma addBitsWithCarry_of_TFT : addBitsWithCarry true false true = (false, true) := by
  sorry

@[simp]
lemma addBitsWithCarry_of_FTT : addBitsWithCarry false true true = (false, true) := by
  sorry

@[simp]
lemma addBitsWithCarry_of_TTF : addBitsWithCarry true true false = (false, true) := by
  sorry

@[simp]
lemma addBitsWithCarry_of_TTT : addBitsWithCarry true true true  = (true, true) := by
  sorry

@[simp]
lemma addListBool_of_empty_left (bs : List Bool) : addListBool [] bs = bs := by
  sorry

@[simp]
lemma addListBool_of_empty_right (bs : List Bool) : addListBool bs [] = bs := by
  sorry

@[simp]
lemma addListBool_of_empty_left_of_carry (bs : List Bool) :
    listBoolToNat (addListBool [] bs true) = listBoolToNat bs + 1 := by
  sorry

@[simp]
lemma addListBool_of_empty_right_of_carry (bs : List Bool) :
    listBoolToNat (addListBool  bs [] true) = listBoolToNat bs + 1 := by
  sorry

/-- BigNum addition on `List Bool` agress with `Nat` addition. -/
theorem addListBool_listBoolToNat (a b : List Bool) (carry : Bool) :
    listBoolToNat (addListBool a b carry) =
    listBoolToNat a + listBoolToNat b + carry.toNat := by
  sorry

/-! ## Addition of BigNum strings -/

/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct (a b : String) : strToNat (add a b) = strToNat a + strToNat b := by
  sorry

/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct' (m n : Nat) : strToNat (add (natToStr m) (natToStr n)) = m + n := by
  sorry
