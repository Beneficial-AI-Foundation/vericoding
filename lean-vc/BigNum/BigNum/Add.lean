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
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_XFF (b : Bool) : addBitsWithCarry  b false false = (b, false) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_FFT : addBitsWithCarry false false true = (true, false) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_TFT : addBitsWithCarry true false true = (false, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_FTT : addBitsWithCarry false true true = (false, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_TTF : addBitsWithCarry true true false = (false, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_TTT : addBitsWithCarry true true true  = (true, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addListBool_of_empty_left (bs : List Bool) : addListBool [] bs = bs := by
  induction bs with
  | nil => simp [addListBool]
  | cons h t ih => simpa [addListBool, addBitsWithCarry_of_FXF]

@[simp]
lemma addListBool_of_empty_right (bs : List Bool) : addListBool bs [] = bs := by
  induction bs with
  | nil => simp [addListBool]
  | cons h t ih =>
    simpa [addListBool]

@[simp]
lemma addListBool_of_empty_left_of_carry (bs : List Bool) :
    listBoolToNat (addListBool [] bs true) = listBoolToNat bs + 1 := by
  induction bs with
  | nil => simp [listBoolToNat, addListBool]
  | cons h t ih =>
    by_cases hh : h
    · have : 2 * (listBoolToNat t + 1) = 2 * listBoolToNat t + 1 + 1 := by ring
      simpa [hh, addListBool, listBoolToNat, ih]
    · simp [hh, addListBool, listBoolToNat, ih]

@[simp]
lemma addListBool_of_empty_right_of_carry (bs : List Bool) :
    listBoolToNat (addListBool  bs [] true) = listBoolToNat bs + 1 := by
  induction bs with
  | nil => simp [listBoolToNat, addListBool]
  | cons h t ih =>
    by_cases hh : h
    · have : 2 * (listBoolToNat t + 1) = 2 * listBoolToNat t + 1 + 1 := by ring
      simpa [hh, addListBool, listBoolToNat, ih]
    · simp [hh, addListBool, listBoolToNat, ih]

/-- BigNum addition on `List Bool` agress with `Nat` addition. -/
theorem addListBool_listBoolToNat (a b : List Bool) (carry : Bool) :
    listBoolToNat (addListBool a b carry) = listBoolToNat a + listBoolToNat b +
    carry.toNat := by
  induction a, b, carry using addListBool.induct with
  | case1 =>
    simp [listBoolToNat, addListBool]
  | case2 carry h =>
    simp [listBoolToNat, addListBool, h]
  | case3 carry b =>
    -- Case: `[], b::bs`
    by_cases carry <;> by_cases b <;> simp_all
  | case4 carry a =>
    -- Case: `a::as, []`
    by_cases carry <;> by_cases a <;> simp_all
  | case5 carry a _ b _ =>
    -- Case: `a::as, b::bs`
    by_cases carry <;> by_cases ha : a <;> by_cases hb : b <;> simp_all [addListBool] <;> ring

/-! ## Addition of BigNum strings -/

/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct (a b : String) : strToNat (add a b) = strToNat a + strToNat b := by
  unfold add
  have A : listBoolToNat (addListBool (strToListBool a) (strToListBool b)) =
      listBoolToNat (strToListBool a) + listBoolToNat (strToListBool b) := by
    simp [addListBool_listBoolToNat]
  have B bs : strToNat (listBoolToStr bs) = listBoolToNat bs := by
    unfold strToNat
    rw [listBoolToStr_strToListBool_id bs]
  rw [B, A]
  exact rfl

/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct' (m n : Nat) : strToNat (add (natToStr m) (natToStr n)) = m + n := by
  simp [add_correct]
