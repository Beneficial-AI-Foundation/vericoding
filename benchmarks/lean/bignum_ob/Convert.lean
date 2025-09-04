import Mathlib
import BigNum.Defs

/-! # Correctness of the definitions related to converting from one representation to another.

Main results:

* `natToStr_strToNat`: converting a natural number to a BigNum string and then back is the identity,
  i.e., `strToNat (natToStr n) = n`.

-/

/-! ## Conversion between `List Bool` and `Nat`. -/

@[simp]
lemma listBoolToNat_of_empty : listBoolToNat [] = 0 := by
  sorry

/-- Convenient lemma for the term which occurs in `listBoolToNat`. -/
@[simp]
lemma listBoolToNat_cons (h : Bool) (t : List Bool) :
    listBoolToNat (h :: t) = 2 * listBoolToNat t + h.toNat :=
  sorry

/-- Converting a `Nat` to a `List Bool` and then back is the identity. -/
@[simp]
lemma natToListBool_listBoolToNat (n : Nat) : listBoolToNat (natToListBool n) = n := by
  sorry

/-! ## Conversion between strings, `List Bool` and `Nat`. -/

@[simp]
theorem boolToChar_charToBool_id (b : Bool) : charToBool (boolToChar b) = b := by
  sorry

/-- Converting from `List Bool` to `String` and back again is the identity. -/
@[simp]
theorem listBoolToStr_strToListBool_id (bools : List Bool) :
    strToListBool (listBoolToStr bools) = bools := by
  sorry

/-- Converting a `Nat` to a string and then back is the identity. -/
@[simp]
lemma natToStr_strToNat (n : Nat) : strToNat (natToStr n) = n := by
  sorry

@[simp]
lemma listBoolToStr_strToNat bs : strToNat (listBoolToStr bs) = listBoolToNat bs := by
  sorry

/-! ## Consistency when removing leading zeros. -/

@[simp]
lemma removeTrailingZeros_of_empty : removeTrailingZeros [] = [] := by
  sorry

@[simp]
lemma removeLeadingZeros_of_false : removeLeadingZeros [false] = [] := by
  sorry

lemma removeLeadingZeros_of_head_true {bs : List Bool} :
    removeLeadingZeros (bs ++ [true]) = (removeLeadingZeros bs) ++ [true] := by
  sorry

lemma removeLeadingZeros_of_head' {bs : List Bool} (h : removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = [] := by
  sorry

lemma removeLeadingZeros_of_head'' {bs : List Bool} (h : ¬ removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = (removeLeadingZeros bs) ++ [false] := by
  sorry

@[simp]
lemma removeTrailingZeros_listBoolToNat (bs : List Bool) :
    listBoolToNat (removeTrailingZeros bs) = listBoolToNat bs := by
  sorry
