import Mathlib
import BigNum.Defs
import BigNum.Convert

/-! # Proofs of correctness of the definitions.

Subtraction of BigNums corresponds to subtraction of the natural numbers.

Main results (NOT COMPLETE):

* `sub_correct`: `strToNat (sub a b) = strToNat a - strToNat b`;
* `sub_correct'`: `strToNat (sub (natToStr m) (natToStr n)) = m - n`.

Remark: if `m < n` then `m - n = 0`.
-/

@[simp]
lemma subListBool_of_empty_of_empty : subListBool [] [] = ([], false) := by
  unfold subListBool
  exact rfl

lemma subBitsWithBorrow_correct (a b borrow : Bool) :
  let (diff, borrowOut) := subBitsWithBorrow a b borrow
  a.toNat + (if borrowOut then 2 else 0) = b.toNat + borrow.toNat + diff.toNat := by
  simp only [subBitsWithBorrow]
  -- Mechanically check all 8 cases
  cases a <;> cases b <;> cases borrow <;> simp

-- lemma subListBoolAux_correct (a b : List Bool) (borrow : Bool) (acc : List Bool) :
--     let (result, finalBorrow) := subListBoolAux a b borrow acc
--     listBoolToNat a + borrow.toNat + listBoolToNat (acc.reverse) * 2 ^ a.length =
--     listBoolToNat b + listBoolToNat result + (if finalBorrow then 2 ^ (max a.length b.length + acc.length) else 0) := by
--   sorry

-- /-- BigNum subtraction on `List Bool` agress with `Nat` subtraction. -/
-- theorem subListBool_no_underflow (a b : List Bool) (borrow : Bool)
--     (h : listBoolToNat a ≥ listBoolToNat b + (if borrow then 1 else 0)) :
--     let (result, borrowOut) := subListBool a b borrow
--     borrowOut = false ∧
--     listBoolToNat result = listBoolToNat a - listBoolToNat b - (if borrow then 1 else 0) := by
--   sorry

-- /-- BigNum subtraction agress with `Nat` subtraction. -/
-- theorem sub_correct (a b : String) : strToNat (sub a b) = strToNat a - strToNat b := by
--   sorry

-- /-- BigNum subtraction agress with `Nat` subtraction. -/
-- theorem sub_correct' (m n : Nat) : strToNat (sub (natToStr m) (natToStr n)) = m - n := by
--   simp [sub_correct]
