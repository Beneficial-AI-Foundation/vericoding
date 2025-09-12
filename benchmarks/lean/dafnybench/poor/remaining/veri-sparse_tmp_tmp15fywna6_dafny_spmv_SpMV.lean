import Std

open Std.Do

/-!
{
  "name": "veri-sparse_tmp_tmp15fywna6_dafny_spmv_SpMV",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: veri-sparse_tmp_tmp15fywna6_dafny_spmv_SpMV",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Recursive sum function that computes dot product of sparse matrix row with vector.
Translated from Dafny's sum function.
-/
def sum (X_val : Array Int) (X_crd : Array Nat) (v : Array Int) (b : Int) (k : Int) : Int :=
  if k ≤ b then
    0
  else
    sum X_val X_crd v (b + 1) k + X_val.get ⟨b⟩ * v.get (X_crd.get ⟨b⟩)

/--
Specification for sum function capturing array bounds and requirements
-/
theorem sum_spec (X_val : Array Int) (X_crd : Array Nat) (v : Array Int) (b k : Int) :
  X_val.size ≥ b ∧ b ≥ 0 ∧
  k ≤ X_val.size ∧
  X_val.size = X_crd.size ∧
  (∀ i, 0 ≤ i ∧ i < X_crd.size → X_crd.get ⟨i⟩ < v.size) →
  sum X_val X_crd v b k ≥ 0 := sorry

/--
Sparse Matrix-Vector multiplication function translated from Dafny's SpMV method
-/
def SpMV (X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat) (v : Array Int) : Array Int :=
  sorry

/--
Specification for SpMV capturing array bounds and correctness requirements
-/
theorem SpMV_spec (X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat) (v : Array Int) :
  X_crd.size ≥ 1 ∧
  X_crd.size = X_val.size ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < X_pos.size → X_pos.get ⟨i⟩ ≤ X_pos.get ⟨j⟩) ∧
  (∀ i, 0 ≤ i ∧ i < X_crd.size → X_crd.get ⟨i⟩ < v.size) ∧
  (∀ i, 0 ≤ i ∧ i < X_pos.size → X_pos.get ⟨i⟩ ≤ X_val.size) ∧
  X_pos.size ≥ 1 →
  let y := SpMV X_val X_crd X_pos v
  y.size + 1 = X_pos.size ∧
  (∀ i, 0 ≤ i ∧ i < y.size → y.get ⟨i⟩ = sum X_val X_crd v (X_pos.get ⟨i⟩) (X_pos.get (i + 1))) := sorry

end DafnyBenchmarks