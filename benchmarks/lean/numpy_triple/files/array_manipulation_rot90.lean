/-  numpy.rot90: Rotate an array by 90 degrees in the plane specified by axes.
    
    For a 2D array, this function rotates the array counterclockwise by 90 degrees
    when k=1. The rotation transforms element at position (i,j) to position 
    (j, n-1-i) for a square matrix of size n×n. Multiple rotations can be achieved 
    by setting k to the desired number of 90-degree rotations.
    
    This specification focuses on square 2D arrays for simplicity.
-/

/-  Specification: rot90 rotates a square 2D matrix by 90 degrees counterclockwise k times.
    
    The specification handles k modulo 4 since four 90-degree rotations return
    to the original orientation:
    - k ≡ 0 (mod 4): No rotation (identity)
    - k ≡ 1 (mod 4): 90° counterclockwise rotation
    - k ≡ 2 (mod 4): 180° rotation  
    - k ≡ 3 (mod 4): 270° counterclockwise (= 90° clockwise)
    
    Mathematical properties:
    1. rot90 is a group action: rot90(m, k1 + k2) = rot90(rot90(m, k1), k2)
    2. rot90(m, 4) = m (period 4)
    3. rot90(m, -k) = rot90(m, 4-k) (inverse rotation)
    
    For a 90° counterclockwise rotation, the transformation is:
    - Element at position (i,j) moves to position (j, n-1-i)
    - This preserves distances and angles (isometry)
    
    Sanity checks:
    - Corner elements rotate correctly: (0,0) → (0,n-1) → (n-1,n-1) → (n-1,0) → (0,0)
    - Center element of odd-sized matrix stays fixed for k=2
    
    Precondition: Matrix is non-empty (n > 0)
    Postcondition: Elements are repositioned according to the rotation formula
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def rot90 {n : Nat} (m : Vector (Vector Float n) n) (k : Int := 1) : 
    Id (Vector (Vector Float n) n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem rot90_spec {n : Nat} (m : Vector (Vector Float n) n) (k : Int) 
    (h_n : n > 0) :
    ⦃⌜n > 0⌝⦄
    rot90 m k
    ⦃⇓result => ⌜let k_mod := k % 4
                 let k_normalized := if k_mod < 0 then k_mod + 4 else k_mod
                 -- Main rotation formulas
                 (k_normalized = 0 → 
                    -- No rotation (identity)
                    ∀ i j : Fin n, (result.get i).get j = (m.get i).get j) ∧
                 (k_normalized = 1 → 
                    -- 90 degrees counterclockwise: (i,j) → (j, n-1-i)
                    ∀ i j : Fin n, 
                    (result.get j).get ⟨n - 1 - i.val, sorry⟩ = (m.get i).get j) ∧
                 (k_normalized = 2 → 
                    -- 180 degrees: (i,j) → (n-1-i, n-1-j)
                    ∀ i j : Fin n, 
                    (result.get ⟨n - 1 - i.val, sorry⟩).get ⟨n - 1 - j.val, sorry⟩ = (m.get i).get j) ∧
                 (k_normalized = 3 → 
                    -- 270 degrees counterclockwise: (i,j) → (n-1-j, i)
                    ∀ i j : Fin n, 
                    (result.get ⟨n - 1 - j.val, sorry⟩).get i = (m.get i).get j) ∧
                 -- Sanity check: corner element rotation for k=1
                 (k_normalized = 1 ∧ n ≥ 2 → 
                    (result.get ⟨0, sorry⟩).get ⟨n - 1, sorry⟩ = (m.get ⟨0, sorry⟩).get ⟨0, sorry⟩) ∧
                 -- Sanity check: for odd n and k=2, center element stays fixed
                 (k_normalized = 2 ∧ n % 2 = 1 → 
                    let center := n / 2
                    (result.get ⟨center, sorry⟩).get ⟨center, sorry⟩ = (m.get ⟨center, sorry⟩).get ⟨center, sorry⟩)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
