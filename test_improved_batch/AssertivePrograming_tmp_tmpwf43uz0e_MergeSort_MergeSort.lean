/-
  Port of AssertivePrograming_tmp_tmpwf43uz0e_MergeSort_MergeSort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MergeSort (a : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem MergeSort_spec (a : Array Int) (b : Array Int) :=
  : b.size == a.size ∧ Sorted(b[..]) ∧ multiset(a[..]) == multiset(b[..])
  := by
  sorry  -- TODO: implement proof


  (h_0 : b ≠ c ∧ b ≠ d ∧ b.size == c.size + d.size)
  (h_1 : Sorted(c[..]) ∧ Sorted(d[..]))
  : Sorted(b[..]) ∧ multiset(b[..]) == multiset(c[..])+multiset(d[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks