import Mathlib
/-!
Implement basic arithmetic for arbitrarily large natural numbers ("bignats") represented as strings
containing only characters "0" and "1".

The implementation in this file uses only structural operations on List Bool, avoiding built-in Nat
operations in the core logic.

- We define natural numbers represented as bitstrings (e.g., "1011").
- All operations are purely structural (not using built-in `+`, `-`, `*` in core logic).
- Operations:
  - `add`: adds two bignat strings,
  - `sub`: computes the difference between two bignat strings
  - `mul`: computes the product of two bignat strings
- Utility functions:
  - `strToNat`: converts bignat string to nat
  - `natToStr`: converts nat to bignat string
- Formal correctness proofs provided for core arithmetic operations
- Every string is a bignat string in the sense that it corresponds to a `Nat`:
  - Most significant digit first as with standard written binary
  - Zero is represented by the empty string
  - zerosy values are `0`, ` `
  - onesy values are `1` and any other character
- Canonical form of a bignat string:
  - No leading `0`s
  - Only the characters `1` or `0`
- Not implemented (only modPowTwo and utility functions done):
  - `modadd`: addition modulo n, i.e., computes a+b mod n
  - `modmul`: multiplication modulo n, , i.e., computes a*b mod n
  - `modexp`: exponentiation modulo n, i.e., computes a^b mod n
-/

/-! ## Define binary addition for list of booleans.

Rather than defining the operations directly for strings, the operations are defined on `List Bool`
as the binary representation with the least significant digit first.

This choice has the convenience
of using `::` since the order is reversed compared to written binary and that any occurences of
`a = '1'` if `a : Char` become simply `a` when `a : Bool`.
-/

/-- Add two bits with carry. -/
def addBitsWithCarry (a b carry : Bool) : Bool × Bool :=
  sorry

/-- Add two binary numbers represented as lists of booleans (least significant bit first). -/
def addListBool (a b : List Bool) (carry : Bool := false) : List Bool :=
  sorry

/-! ## Conversion between `List Bool` and `Nat`. -/

/-- Convert `List Bool` to a `Nat`. -/
def listBoolToNat : List Bool → Nat
  | [] => 0
  | h::t => 2 * listBoolToNat t + h.toNat

/-- Convert a `Nat` to a `List Bool`. -/
def natToListBool (n : Nat) : List Bool :=
  if n = 0 then []
  else (if n % 2 = 1 then true else false) :: natToListBool (n / 2)

/-! ## Conversion between strings, `List Bool` and `Nat`. -/

/-- Every character is interpreted as `0` or `1`: both `0` and ` ` are interpreted as `0`, anything
else is interpreted as `1`. -/
def charToBool : Char → Bool
  | '0' => false
  | ' ' => false
  | _   => true

/-- Convert from `Bool` to `Char`. -/
def boolToChar (b : Bool) : Char :=
  if b then '1' else '0'

/-- Convert `String` to `List Bool`. -/
def strToListBool (s : String) : List Bool :=
  s.toList.reverse.map charToBool

/-- Convert `List Bool` back to `String`. -/
def listBoolToStr (bs : List Bool) : String :=
  String.mk <| (bs.reverse).map boolToChar

/-- Convert any string to a `Nat` by interpreting the characters as bit values.
- Zerosy values are `0` or ` `;
- Onesy values are `1` and any other character.
Most significant digit first as with standard written binary. -/
def strToNat (s : String) := listBoolToNat (strToListBool s)

def natToStr (n : Nat) : String := listBoolToStr (natToListBool n)

/-! ## Clean by removing leading zeros of `List Bool`. -/

/-- Remove leading falses. -/
def removeLeadingZeros (bs : List Bool) : List Bool :=
  match bs with
  | [] => []
  | false :: tail => removeLeadingZeros tail -- remove false and continue
  | true :: _ => bs  -- begins with true, don't remove anything

/-- Remove trailing zeros. -/
def removeTrailingZeros (bs : List Bool) : List Bool :=
  (removeLeadingZeros bs.reverse).reverse

/-! ## Define addition for binary numbers written as strings. -/

/-- Addition of two binary numbers represented as strings. -/
def add (a b : String) : String :=
  sorry

/-! ## Define binary subtraction for list of booleans. -/

/-- Subtract two bits with borrow. -/
def subBitsWithBorrow (a b borrow : Bool) : Bool × Bool :=
  sorry

def subListBoolAux (a b : List Bool) (borrow : Bool) (acc : List Bool) : List Bool × Bool :=
  sorry

def subListBool (a b : List Bool) (borrow : Bool := false) : List Bool × Bool :=
  sorry

/-- Subtract two binary numbers, returning just the result or zero if negative. -/
def subListBool' (a b : List Bool) : List Bool :=
  sorry

/-! ## Define subtraction for binary numbers written as strings. -/

-- new version
/-- Subtraction of two binary numbers represented as strings. -/
def sub (a b : String) : String :=
  sorry

-- Examples
-- #eval sub "1001" "11"
-- #eval sub "1001" "001"
-- #eval sub "10" "11"
-- #eval strToNat (sub (natToStr 15) (natToStr 3))
-- #eval strToNat (sub (natToStr 7) (natToStr 0))
-- #eval strToNat (sub (natToStr 7) (natToStr 8))

/-! ## Define multiplication for list of booleans -/

def shiftLeft (bs : List Bool) : List Bool :=
  sorry

-- #eval shiftLeft []
-- #eval shiftLeft [true]

def mulListBool_aux (a b : List Bool) (acc : List Bool) : List Bool :=
  sorry

-- #eval mulListBool_aux [true, true] [] [true, false]

def mulListBool (a b : List Bool) : List Bool :=
  sorry

-- Example usage:
-- #eval mulListBool [true, false, true] [true, true] -- 5 * 3 = 15
-- Expected: [true, true, true, true] (15 in binary: 1111)

/-! ## Define multiplication for binary numbers written as strings. -/

/-- Subtraction of two binary numbers represented as strings. -/
def mul (a b : String) : String :=
  sorry

-- #eval mul "1001" "11"
-- #eval mul "1001" "001"
-- #eval mul "10" "11"
-- #eval strToNat (mul (natToStr 7) (natToStr 4))


/-! ## Helper functions -/

/-- Check if a List Bool has no bits set. -/
def isZero (bs : List Bool) : Prop :=
  sorry

/-- Check if a List Bool has exactly one bit set. -/
def isPowTwo (bs : List Bool) : Prop :=
  sorry

/-- Check if a number is one -/
def isOne (bs : List Bool) : Prop :=
  sorry

/-! ## Modular Exponentiation for Power-of-2 Modulus

Implementation of a mod c when c = 2^n. In this case we can use simple bitwise operations.
For c = 2^n, taking mod c is equivalent to keeping only the lowest n bits.
-/

/-- Use a list `bs` as a counter to remove bits from `as`. -/
def modPowTwoListBool (as counter : List Bool) : List Bool :=
  sorry

/-! ## Define mod for binary numbers written as strings. -/

def modPowTwo (a b : String) : String :=
  sorry

/-- Check that the string represents a binary number which is a power of two. -/
def isPowTwo' (a : String) : Prop := isPowTwo (strToListBool a)

-- Examples
-- #eval modPowTwo "1100" "100"
-- #eval modPowTwo "001100" "100"
-- #eval modPowTwo "110110" "100"
-- #eval modPowTwo "110110" "0"
-- #eval strToNat <| modPowTwo (natToStr 13) (natToStr 4)
-- #eval strToNat <| modPowTwo (natToStr 13) (natToStr 1)
-- #eval strToNat <| modPowTwo (natToStr 13) (natToStr 0)


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

/-- BigNum addition agrees with `Nat` addition. -/
theorem add_correct (a b : String) : strToNat (add a b) = strToNat a + strToNat b := by
  sorry

/-- BigNum addition agrees with `Nat` addition. -/
theorem add_correct' (m n : Nat) : strToNat (add (natToStr m) (natToStr n)) = m + n := by
  sorry


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


/-! # Proofs of correctness of the definitions.

Subtraction of BigNums corresponds to subtraction of the natural numbers.

Main results (NOT COMPLETE):

* `sub_correct`: `strToNat (sub a b) = strToNat a - strToNat b`;
* `sub_correct'`: `strToNat (sub (natToStr m) (natToStr n)) = m - n`.

Remark: if `m < n` then `m - n = 0`.
-/

@[simp]
lemma subListBool_of_empty_of_empty : subListBool [] [] = ([], false) := by
  sorry

lemma subBitsWithBorrow_correct (a b borrow : Bool) :
    let (diff, borrowOut) := subBitsWithBorrow a b borrow
    a.toNat + (if borrowOut then 2 else 0) = b.toNat + borrow.toNat + diff.toNat := by
  sorry

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
