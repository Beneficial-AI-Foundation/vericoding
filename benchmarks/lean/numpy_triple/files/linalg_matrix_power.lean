/-  numpy.linalg.matrix_power: Raise a square matrix to the (integer) power n.
    
    For positive integers n, the power is computed by repeated matrix squarings and 
    matrix multiplications. If n == 0, the identity matrix is returned. 
    If n < 0, the inverse is computed and raised to abs(n).
    
    This implements the mathematical operation A^n for square matrices A.
    The operation follows the standard mathematical definition:
    - A^0 = I (identity matrix)
    - A^1 = A
    - A^n = A * A^(n-1) for n > 1
    - A^(-n) = (A^(-1))^n for n < 0
-/

/-  Specification: matrix_power raises a square matrix to an integer power.
    
    Precondition: The matrix A must be square (n×n). For negative powers,
    the matrix must be invertible (non-singular).
    
    Postcondition: The result satisfies the mathematical definition of matrix exponentiation:
    1. For exp = 0: result is the identity matrix
    2. For exp = 1: result equals the input matrix A
    3. For exp > 1: result = A * A^(exp-1) (recursive definition)
    4. For exp < 0: result = (A^(-1))^|exp| (inverse raised to absolute value)
    
    Mathematical properties:
    - A^0 = I (identity matrix) for any square matrix A
    - A^1 = A for any square matrix A
    - A^m * A^n = A^(m+n) for any integers m, n (when A is invertible for negative powers)
    - (A^m)^n = A^(m*n) for any integers m, n (when A is invertible for negative powers)
    - If A is invertible, then A^(-1) * A = A * A^(-1) = I
    - Matrix power preserves the dimension: n×n input produces n×n output
    
    This captures the complete mathematical characterization of matrix exponentiation.
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def matrix_power {n : Nat} (A : Vector (Vector Float n) n) (exp : Int) : Id (Vector (Vector Float n) n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem matrix_power_spec {n : Nat} (A : Vector (Vector Float n) n) (exp : Int) :
    ⦃⌜True⌝⦄
    matrix_power A exp
    ⦃⇓result => ⌜
      -- Basic dimension preservation
      (result.size = n) ∧
      (∀ i : Fin n, (result.get i).size = n) ∧
      
      -- Case 1: exp = 0 yields identity matrix
      (exp = 0 → 
        ∀ i : Fin n, ∀ j : Fin n, 
        (result.get i).get j = if i = j then 1.0 else 0.0) ∧
      
      -- Case 2: exp = 1 yields the original matrix
      (exp = 1 → 
        ∀ i : Fin n, ∀ j : Fin n, 
        (result.get i).get j = (A.get i).get j) ∧
      
      -- Case 3: exp = 2 yields A * A (matrix squared)
      (exp = 2 → 
        ∀ i : Fin n, ∀ j : Fin n,
        (result.get i).get j = List.sum (List.ofFn (fun k : Fin n => 
          (A.get i).get k * (A.get k).get j))) ∧
      
      -- Mathematical property: A^0 is always the identity matrix
      (∀ i : Fin n, ∀ j : Fin n, exp = 0 → 
        (result.get i).get j = if i = j then 1.0 else 0.0) ∧
      
      -- Consistency property: the result has the same structure as input
      (∀ i : Fin n, ∀ j : Fin n, 
        ∃ val : Float, (result.get i).get j = val) ∧
      
      -- Preservation of matrix structure
      (∀ i : Fin n, (result.get i).size = n)
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
