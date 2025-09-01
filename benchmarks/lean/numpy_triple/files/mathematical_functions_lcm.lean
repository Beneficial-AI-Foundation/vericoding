/- 
{
  "name": "numpy.lcm",
  "description": "Returns the lowest common multiple of |x1| and |x2|",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.lcm.html",
  "doc": "Returns the lowest common multiple of |x1| and |x2|.",
}
-/

/-  numpy.lcm: Returns the lowest common multiple of |x1| and |x2| element-wise.

    Computes the lowest common multiple (LCM) of the absolute values of 
    the elements in x1 and x2. The LCM is the smallest non-negative integer 
    that is a multiple of both |x1| and |x2|.

    Mathematical Properties:
    - lcm(a, b) = lcm(b, a) (commutativity)
    - lcm(a, b) * gcd(a, b) = |a * b| (fundamental relationship)
    - lcm(0, b) = lcm(a, 0) = 0 (zero property)
    - lcm(a, b) ≥ 0 (non-negativity)
    - |a| divides lcm(a, b) and |b| divides lcm(a, b) (divisibility)
    - lcm(a, b) is minimal among all positive integers divisible by both |a| and |b|

    Examples:
    - lcm(4, 6) = 12
    - lcm(-4, 6) = 12 (uses absolute values)
    - lcm(0, 5) = 0 (LCM with zero is always zero)
    - lcm(8, 12) = 24
    - lcm(7, 11) = 77 (coprime numbers)
-/

/-  Specification: lcm returns a vector where each element is the lowest 
    common multiple of the absolute values of the corresponding elements 
    from x1 and x2.

    Precondition: True (no special preconditions)
    
    Postcondition: 
    1. Each element of the result is the LCM of |x1[i]| and |x2[i]|
    2. The result satisfies the mathematical properties of LCM:
       - Non-negativity: lcm(a, b) ≥ 0 (always true by definition)
       - Zero property: lcm(0, b) = lcm(a, 0) = 0
       - Commutativity: lcm(a, b) = lcm(b, a) (implicit in Int.lcm)
       - Relationship with GCD: lcm(a, b) * gcd(a, b) = |a * b|
       - Divisibility: |a| divides lcm(a, b) and |b| divides lcm(a, b)
       - Minimality: lcm(a, b) is the smallest non-negative integer divisible by both |a| and |b| (when both are non-zero)
    3. Special cases:
       - When either input is zero, the result is zero
       - When inputs are coprime (gcd = 1), lcm = |a * b|
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def lcm {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem lcm_spec {n : Nat} (x1 x2 : Vector Int n) :
    ⦃⌜True⌝⦄
    lcm x1 x2
    ⦃⇓result => ⌜-- Basic correctness: each element is the LCM of corresponding elements
                 (∀ i : Fin n, result.get i = (Int.lcm (x1.get i) (x2.get i) : Int)) ∧
                 -- Non-negativity: LCM is always non-negative
                 (∀ i : Fin n, result.get i ≥ 0) ∧
                 -- Zero property: LCM with zero is zero
                 (∀ i : Fin n, (x1.get i = 0 ∨ x2.get i = 0) → result.get i = 0) ∧
                 -- Commutativity: LCM is commutative
                 (∀ i : Fin n, result.get i = (Int.lcm (x2.get i) (x1.get i) : Int)) ∧
                 -- Fundamental LCM-GCD relationship: lcm(a,b) * gcd(a,b) = |a * b|
                 (∀ i : Fin n, x1.get i ≠ 0 → x2.get i ≠ 0 → 
                    Int.natAbs (result.get i) * Int.gcd (x1.get i) (x2.get i) = Int.natAbs (x1.get i) * Int.natAbs (x2.get i)) ∧
                 -- Divisibility: both absolute values divide the LCM
                 (∀ i : Fin n, x1.get i ≠ 0 → x2.get i ≠ 0 → 
                    (Int.natAbs (x1.get i) : Int) ∣ result.get i ∧ (Int.natAbs (x2.get i) : Int) ∣ result.get i) ∧
                 -- Minimality: LCM is the smallest non-negative integer divisible by both absolute values
                 (∀ i : Fin n, ∀ (m : Int), m ≥ 0 → 
                    (Int.natAbs (x1.get i) : Int) ∣ m → (Int.natAbs (x2.get i) : Int) ∣ m → 
                    x1.get i ≠ 0 → x2.get i ≠ 0 → result.get i ≤ m) ∧
                 -- Special case: when both are non-zero, LCM is positive
                 (∀ i : Fin n, x1.get i ≠ 0 → x2.get i ≠ 0 → result.get i > 0)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
