/-!
# CHALLENGE 1:

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
  | [] => sorry
  | h::t => sorry

/-- Convert a `Nat` to a `List Bool`. -/
def natToListBool (n : Nat) : List Bool :=
  sorry

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
  sorry

/-- Convert `List Bool` back to `String`. -/
def listBoolToStr (bs : List Bool) : String :=
  sorry

/-- Convert any string to a `Nat` by interpreting the characters as bit values.
- Zerosy values are `0` or ` `;
- Onesy values are `1` and any other character.
Most significant digit first as with standard written binary. -/
def strToNat (s : String) :=
  sorry

def natToStr (n : Nat) : String :=
  sorry

/-! ## Clean by removing leading zeros of `List Bool`. -/

/-- Remove leading falses. -/
def removeLeadingZeros (bs : List Bool) : List Bool :=
  sorry

/-- Remove trailing zeros. -/
def removeTrailingZeros (bs : List Bool) : List Bool :=
  sorry

/-! ## Define addition for binary numbers written as strings. -/

/-- Addition of two binary numbers represented as strings. -/
def add (a b : String) : String :=
  sorry

-- Example
#eval add "1001" "11"

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
#eval sub "1001" "11"
#eval sub "1001" "001"
#eval sub "10" "11"
#eval strToNat (sub (natToStr 15) (natToStr 3))
#eval strToNat (sub (natToStr 7) (natToStr 0))
#eval strToNat (sub (natToStr 7) (natToStr 8))

/-! ## Define multiplication for list of booleans -/

def shiftLeft (bs : List Bool) : List Bool :=
  sorry

#eval shiftLeft []
#eval shiftLeft [true]

def mulListBool_aux (a b : List Bool) (acc : List Bool) : List Bool :=
  sorry

#eval mulListBool_aux [true, true] [] [true, false]

def mulListBool (a b : List Bool) : List Bool :=
  sorry

-- Example usage:
#eval mulListBool [true, false, true] [true, true] -- 5 * 3 = 15
-- Expected: [true, true, true, true] (15 in binary: 1111)

/-! ## Define multiplication for binary numbers written as strings. -/

/-- Subtraction of two binary numbers represented as strings. -/
def mul (a b : String) : String :=
  sorry

#eval mul "1001" "11"
#eval mul "1001" "001"
#eval mul "10" "11"
#eval strToNat (mul (natToStr 7) (natToStr 4))


/-! ## Helper functions -/

/-- Check if a List Bool has no bits set. -/
def isZero (bs : List Bool) : Prop := match bs with
  sorry

/-- Check if a List Bool has exactly one bit set. -/
def isPowTwo (bs : List Bool) : Prop := match bs with
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
#eval modPowTwo "1100" "100"
#eval modPowTwo "001100" "100"
#eval modPowTwo "110110" "100"
#eval modPowTwo "110110" "0"
#eval strToNat <| modPowTwo (natToStr 13) (natToStr 4)
#eval strToNat <| modPowTwo (natToStr 13) (natToStr 1)
#eval strToNat <| modPowTwo (natToStr 13) (natToStr 0)
#eval 13 % 4
#eval 13 % 1
#eval 13 % 0
