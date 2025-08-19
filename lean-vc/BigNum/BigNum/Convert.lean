import Mathlib
import BigNum.Defs

/-! # Correctness of the definitions related to converting from one representation to another.

Main results:

* `natToStr_strToNat`: converting a natural number to a BigNum string and then back is the identity,
  i.e., `strToNat (natToStr n) = n`.

-/

/-! ## Conversion between `List Bool` and `Nat`. -/

@[simp]
lemma listBoolToNat_of_empty : listBoolToNat [] = 0 := by rfl

/-- Convenient lemma for the term which occurs in `listBoolToNat`. -/
@[simp]
lemma listBoolToNat_cons (h : Bool) (t : List Bool) :
  listBoolToNat (h :: t) = 2 * listBoolToNat t + h.toNat := rfl

/-- Converting a `Nat` to a `List Bool` and then back is the identity. -/
@[simp]
lemma natToListBool_listBoolToNat (n : Nat) : listBoolToNat (natToListBool n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 0
    · simp [h, natToListBool, listBoolToNat]
    · suffices 2 * listBoolToNat (natToListBool (n / 2)) + (decide (n % 2 = 1)).toNat = n by
        unfold natToListBool
        simpa [h, listBoolToNat_cons]
      have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
      rw [ih (n / 2) div_lt]
      by_cases hc : n % 2 = 1
      all_goals
      · simp [hc]; omega

/-! ## Conversion between strings, `List Bool` and `Nat`. -/

@[simp]
theorem boolToChar_charToBool_id (b : Bool) : charToBool (boolToChar b) = b := by
  by_cases hb : b
  all_goals
  · simp [hb, charToBool, boolToChar]

/-- Converting from `List Bool` to `String` and back again is the identity. -/
@[simp]
theorem listBoolToStr_strToListBool_id (bools : List Bool) :
    strToListBool (listBoolToStr bools) = bools := by
  induction bools with
  | nil =>
    simp [strToListBool, listBoolToStr]
  | cons bh bt ih =>
    suffices h : List.map (charToBool ∘ boolToChar) bt = bt by
      simpa [strToListBool, listBoolToStr]
    refine List.map_id'' (fun a ↦ ?_) bt
    exact boolToChar_charToBool_id a

/-- Converting a `Nat` to a string and then back is the identity. -/
@[simp]
lemma natToStr_strToNat (n : Nat) : strToNat (natToStr n) = n := by
  simp [strToNat, natToStr]

@[simp]
lemma listBoolToStr_strToNat bs : strToNat (listBoolToStr bs) = listBoolToNat bs := by
    unfold strToNat
    rw [listBoolToStr_strToListBool_id bs]

/-! ## Consistency when removing leading zeros. -/

@[simp]
lemma removeTrailingZeros_of_empty : removeTrailingZeros [] = [] := by
  simp [removeTrailingZeros, removeLeadingZeros]

@[simp]
lemma removeLeadingZeros_of_false : removeLeadingZeros [false] = [] := by
  simp [removeLeadingZeros]

lemma removeLeadingZeros_of_head_true {bs : List Bool} :
    removeLeadingZeros (bs ++ [true]) = (removeLeadingZeros bs) ++ [true] := by
  induction bs using removeLeadingZeros.induct with
    | case1 => tauto
    | case2 t ih => simpa
    | case3 t => simp [removeTrailingZeros, removeLeadingZeros]

lemma removeLeadingZeros_of_head' {bs : List Bool} (h : removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = [] := by
  induction bs with
    | nil => simp
    | cons head tail ih =>
      have hc : head = false := by
        by_contra! hc
        simp [hc, removeLeadingZeros] at h
      replace h : removeLeadingZeros tail = [] := by
        simp_all [hc, removeLeadingZeros]
      simp [hc, removeLeadingZeros, ih h]

lemma removeLeadingZeros_of_head'' {bs : List Bool} (h : ¬ removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = (removeLeadingZeros bs) ++ [false] := by
  induction bs with
    | nil =>
      simp [removeLeadingZeros] at h
    | cons head tail ih =>
      by_cases hc : head
      · rw [hc] at h ⊢
        simp [removeLeadingZeros]
      · rw [eq_false_of_ne_true hc] at h ⊢
        have : ¬removeLeadingZeros tail = [] := by
          simp_all [removeLeadingZeros]
        simp [removeLeadingZeros, ih this]

@[simp]
lemma removeTrailingZeros_listBoolToNat (bs : List Bool) :
    listBoolToNat (removeTrailingZeros bs) = listBoolToNat bs := by
  induction bs with
    | nil => simp
    | cons h t ih =>
      simp [removeTrailingZeros, removeLeadingZeros]
      by_cases hh : h
      · simp [hh, removeLeadingZeros_of_head_true,  ← ih, removeTrailingZeros, removeLeadingZeros]
      · by_cases ht : removeLeadingZeros t.reverse = []
        · unfold removeTrailingZeros at ih
          rw [ht, List.reverse_nil, listBoolToNat_of_empty] at ih
          simp [eq_false_of_ne_true hh, removeLeadingZeros_of_head' ht, ← ih]
        · simpa [eq_false_of_ne_true hh, removeLeadingZeros_of_head'' ht]
