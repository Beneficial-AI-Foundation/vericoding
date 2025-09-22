-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_repr (num : Int) (width : Option Nat := none) : Id String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
  sorry
-- </vc-theorems>