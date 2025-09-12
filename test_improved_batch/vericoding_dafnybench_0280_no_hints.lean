/-
  Port of vericoding_dafnybench_0280_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def RowColumnProduct (m1 : array2<int>) (m2 : array2<int>) (row : Nat) (column : Nat) : Int :=
  RowColumnProductFrom(m1, m2, row, column, 0)

def RowColumnProductFrom (m1 : array2<int>) (m2 : array2<int>) (row : Nat) (column : Nat) (k : Nat) : Int :=
  sorry  -- TODO: implement complex function body

def multiply (m1 : array2<int>) (m2 : array2<int>) : array2<int> :=
  sorry  -- TODO: implement function body

theorem multiply_spec (m1 : array2<int>) (m2 : array2<int>) (m3 : array2<int>) :=
  (h_0 : m1 ≠ null ∧ m2 ≠ null)
  (h_1 : m1.Length1 == m2.Length0)
  : m3 ≠ null ∧ m3.Length0 == m1.Length0 ∧ m3.Length1 == m2.Length1 ∧ ∀ i, j | 0 ≤ i < m3.Length0 ∧ 0 ≤ j < m3.Length1 ::
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks