/- 
{
  "name": "numpy.binary_repr",
  "category": "Output formatting",
  "description": "Return the binary representation of the input number as a string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.binary_repr.html",
  "doc": "Return the binary representation of the input number as a string.\n\nFor negative numbers, if width is not given, a minus sign is added to the front. If width is given, the two's complement of the number is returned, with respect to that width.\n\nIn a two's-complement system negative numbers are represented by the two's complement of the absolute value. This is the most common method of representing signed integers on computers. A N-bit two's-complement system can represent every integer in the range -2^(N-1) to +2^(N-1)-1.\n\nParameters\n----------\nnum : int\n    Only an integer decimal number can be used.\nwidth : int, optional\n    The length of the returned string if num is positive, or the length of the two's complement if num is negative, provided that width is at least a sufficient number of bits for num to be represented in the designated form.\n\nReturns\n-------\nbin : str\n    Binary representation of num or two's complement of num.\n\nNotes\n-----\nbinary_repr is equivalent to using base_repr with base 2, but about 25x faster.\n\nReferences\n----------\n.. [1] Wikipedia, \"Two's complement\",\n    https://en.wikipedia.org/wiki/Two's_complement\n\nExamples\n--------\n>>> np.binary_repr(3)\n'11'\n>>> np.binary_repr(-3)\n'-11'\n>>> np.binary_repr(3, width=4)\n'0011'\n\nThe two's complement is returned when the input number is negative and width is specified:\n\n>>> np.binary_repr(-3, width=3)\n'101'\n>>> np.binary_repr(-3, width=5)\n'11101'",
}
-/

/-  Return the binary representation of the input number as a string.
    For negative numbers, if width is not given, a minus sign is added to the front.
    If width is given, the two's complement of the number is returned. -/

/-  Specification: binary_repr correctly converts integers to binary strings with proper
    handling of negative numbers (signed representation without width, two's complement with width) -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Helper function to convert a natural number to its binary string representation -/
def natToBinaryString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec loop (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else loop (m / 2) (if m % 2 = 0 then "0" ++ acc else "1" ++ acc)
    loop n ""
/-- Helper function to check if a string represents a valid binary number -/
def isValidBinary (s : String) : Bool :=
  s.length > 0 && s.all (fun c => c = '0' || c = '1')
/-- Helper function to check if a string represents a valid signed binary number -/
def isValidSignedBinary (s : String) : Bool :=
  if s.startsWith "-" then
    isValidBinary (s.drop 1)
  else
    isValidBinary s

-- <vc-helpers>
-- </vc-helpers>

def binary_repr (num : Int) (width : Option Nat := none) : Id String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem binary_repr_spec (num : Int) (width : Option Nat := none) :
    ⦃⌜width.map (· ≥ 1) |>.getD true⌝⦄
    binary_repr num width
    ⦃⇓result => ⌜
      -- Result is a valid binary string (possibly with sign)
      (width.isNone → isValidSignedBinary result) ∧
      (width.isSome → isValidBinary result) ∧
      
      -- Length constraints
      (width.isSome → result.length = width.get!) ∧
      
      -- Positive numbers: standard binary representation
      (num ≥ 0 ∧ width.isNone → 
        result = natToBinaryString num.natAbs) ∧
      
      -- Positive numbers with width: padded with zeros
      (num ≥ 0 ∧ width.isSome → 
        ∃ (binary : String), binary = natToBinaryString num.natAbs ∧
        result = String.mk (List.replicate (width.get! - binary.length) '0') ++ binary) ∧
      
      -- Negative numbers without width: signed representation
      (num < 0 ∧ width.isNone → 
        result = "-" ++ natToBinaryString num.natAbs) ∧
      
      -- Negative numbers with width: two's complement
      (num < 0 ∧ width.isSome → 
        let w := width.get!
        let twoComp := (2^w : Int) + num
        -- Two's complement is in valid range
        (0 ≤ twoComp ∧ twoComp < 2^w) ∧
        -- Result represents the two's complement
        result = natToBinaryString twoComp.natAbs ∧
        -- Padded with 1s if needed
        result.length = w)
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
