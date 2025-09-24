-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def operation (a b : Nat) : Nat := sorry

def isPowerOf2 (n : Nat) : Bool := sorry

-- Operations are symmetric between powers of 2
-- </vc-definitions>

-- <vc-theorems>
theorem operation_symmetry (a b : Nat) :
  a ≠ 0 → b ≠ 0 → isPowerOf2 a → isPowerOf2 b → 
  operation a b = operation b a := sorry

-- Number of operations is non-negative

theorem operation_positive (n target : Nat) : 
  n ≠ 0 → operation n target ≥ 0 := sorry

-- Triangle inequality through power of 2

theorem operation_triangle_inequality (a b power2 : Nat) :
  a ≠ 0 → b ≠ 0 → isPowerOf2 power2 →
  operation a b ≤ operation a power2 + operation power2 b := sorry

-- Self operation vs through power of 2

theorem operation_with_self (n pow2 : Nat) :
  n ≠ 0 → isPowerOf2 pow2 →
  operation n n ≤ 2 * operation n pow2 := sorry
-- </vc-theorems>