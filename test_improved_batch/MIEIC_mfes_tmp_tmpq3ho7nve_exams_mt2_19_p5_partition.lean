/-
  Port of MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p5_partition.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def partition (a : Array T) : Int :=
  sorry  -- TODO: implement function body

theorem partition_spec (a : Array T) (pivotPos : Int) :=
  (h_0 : a.size > 0)
  : 0 ≤ pivotPos < a.size ∧ ∀ i :: 0 ≤ i < pivotPos → a[i]! < a[pivotPos]! ∧ ∀ i :: pivotPos < i < a.size → a[i]! ≥ a[pivotPos]! ∧ multiset(a[..]) == multiset(old(a[..]))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks