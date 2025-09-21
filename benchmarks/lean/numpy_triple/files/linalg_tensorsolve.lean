-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tensorsolve {n : Nat} (a : Vector (Vector Float n) n) (b : Vector Float n) : 
    Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tensorsolve_spec {n : Nat} (a : Vector (Vector Float n) n) (b : Vector Float n)
    (h_invertible : ∃ a_inv : Vector (Vector Float n) n,
      -- Matrix a is invertible (has an inverse)
      (∀ i j : Fin n,
        let matrix_mult_ij := List.sum (List.ofFn fun k : Fin n => 
          (a.get i).get k * (a_inv.get k).get j)
        matrix_mult_ij = if i = j then 1.0 else 0.0) ∧
      (∀ i j : Fin n,
        let matrix_mult_ij := List.sum (List.ofFn fun k : Fin n => 
          (a_inv.get i).get k * (a.get k).get j)
        matrix_mult_ij = if i = j then 1.0 else 0.0)) :
    ⦃⌜∃ a_inv : Vector (Vector Float n) n,
      (∀ i j : Fin n,
        let matrix_mult_ij := List.sum (List.ofFn fun k : Fin n => 
          (a.get i).get k * (a_inv.get k).get j)
        matrix_mult_ij = if i = j then 1.0 else 0.0) ∧
      (∀ i j : Fin n,
        let matrix_mult_ij := List.sum (List.ofFn fun k : Fin n => 
          (a_inv.get i).get k * (a.get k).get j)
        matrix_mult_ij = if i = j then 1.0 else 0.0)⌝⦄
    tensorsolve a b
    ⦃⇓x => ⌜(∀ i : Fin n,
              List.sum (List.ofFn fun j : Fin n => 
                (a.get i).get j * x.get j) = b.get i) ∧
            (∀ y : Vector Float n,
              (∀ i : Fin n,
                List.sum (List.ofFn fun j : Fin n => 
                  (a.get i).get j * y.get j) = b.get i) → 
              y = x) ∧
            (∀ a_inv : Vector (Vector Float n) n,
              (∀ i j : Fin n, 
                let matrix_mult_ij := List.sum (List.ofFn fun k : Fin n => 
                  (a.get i).get k * (a_inv.get k).get j)
                matrix_mult_ij = if i = j then 1.0 else 0.0) →
              (∀ i : Fin n,
                x.get i = List.sum (List.ofFn fun j : Fin n => 
                  (a_inv.get i).get j * b.get j)))⌝⦄ := by
  sorry
-- </vc-theorems>