/- 
{
  "name": "numpy.linalg.vector_norm",
  "category": "Norms and numbers",
  "description": "Compute vector norm",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.vector_norm.html",
  "doc": "Computes the vector norm of a vector.\n\nThis function is able to return one of an infinite number of vector norms, depending on the value of the ord parameter.",
}
-/

/-  numpy.linalg.vector_norm: Compute the p-norm of a vector for a given order p.
    
    This function computes vector norms of different orders (p-norms).
    For a vector x and order p, the p-norm is defined as:
    ||x||_p = (sum(|x[i]|^p))^(1/p) for p ≥ 1
    
    Special cases:
    - p = 1: Manhattan norm (sum of absolute values)
    - p = 2: Euclidean norm (square root of sum of squares)
    - p = ∞: Maximum norm (largest absolute value)
    - p = -∞: Minimum norm (smallest absolute value)
    - p = 0: Zero norm (count of non-zero elements)
    
    This implementation focuses on the most common p-norm cases for 1D vectors.
-/

/-  Specification: vector_norm computes the p-norm of a vector for various values of p.
    
    The p-norm is a generalization of the common vector norms used in numerical computing.
    This specification covers the mathematical definition and key properties of p-norms.
    
    Mathematical definition:
    - For p ≥ 1: ||x||_p = (Σᵢ |xᵢ|^p)^(1/p)
    - For p = 1: ||x||_1 = Σᵢ |xᵢ| (Manhattan norm)
    - For p = 2: ||x||_2 = √(Σᵢ xᵢ²) (Euclidean norm)
    - For p = 0: ||x||_0 = count of non-zero elements
    
    Key properties verified:
    1. Definition: For p ≥ 1, result equals (sum of |xi|^p)^(1/p)
    2. Non-negativity: norm(x, p) ≥ 0 for all x and valid p
    3. Definiteness: norm(x, p) = 0 iff x is zero vector (for p > 0)
    4. Special cases: p=1 (Manhattan), p=2 (Euclidean), p=0 (zero norm)
    5. Empty vector: norm of empty vector is 0
    
    Preconditions:
    - p must be a non-negative real number
    - For p = 0, it counts non-zero elements (special case)
    - For p ≥ 1, it computes the standard p-norm
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def vector_norm {n : Nat} (x : Vector Float n) (p : Float) : Id Float :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem vector_norm_spec {n : Nat} (x : Vector Float n) (p : Float) 
    (h_valid_p : p ≥ 0) :
    ⦃⌜p ≥ 0⌝⦄
    vector_norm x p
    ⦃⇓result => ⌜result ≥ 0 ∧
                 (n = 0 → result = 0) ∧
                 (p = 2 → result = Float.sqrt (List.sum (x.toList.map (fun xi => xi * xi)))) ∧
                 (p = 1 → result = List.sum (x.toList.map (fun xi => Float.abs xi))) ∧
                 (p = 0 → result = Float.ofNat (x.toList.filter (fun xi => xi != 0)).length) ∧
                 (p > 1 → 
                   result = Float.pow (List.sum (x.toList.map (fun xi => Float.pow (Float.abs xi) p))) (1 / p)) ∧
                 (result = 0 ↔ (p > 0 ∧ ∀ i : Fin n, x.get i = 0))⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
