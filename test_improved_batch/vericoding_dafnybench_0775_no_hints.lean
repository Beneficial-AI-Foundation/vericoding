/-
  Port of vericoding_dafnybench_0775_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
  if k ≤ b then 0 else  sum(X_val, X_crd, v, b + 1, k) + X_val[b]! * v[X_crd[b]!]

def SpMV (X_val : Array Int) (X_crd : array<nat>) (X_pos : array<nat>) (v : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem SpMV_spec (X_val : Array Int) (X_crd : array<nat>) (X_pos : array<nat>) (v : Array Int) (y : Array Int) :=
  (h_0 : X_crd.size ≥ 1)
  (h_1 : X_crd.size == X_val.size;)
  (h_2 : ∀ i, j :: 0 ≤ i < j < X_pos.size → X_pos[i]! ≤ X_pos[j]!;)
  (h_3 : ∀ i :: 0 ≤ i < X_crd.size → X_crd[i]! < v.size)
  (h_4 : ∀ i :: 0 ≤ i < X_pos.size → X_pos[i]! ≤ X_val.size)
  (h_5 : X_pos.size ≥ 1)
  : y.size + 1 == X_pos.size ∧ ∀ i :: 0 ≤ i < y.size → y[i]! == sum(X_val, X_crd, v, X_pos[i]!, X_pos[i + 1])
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks