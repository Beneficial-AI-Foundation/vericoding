/-
  Port of vericoding_dafnybench_0006_no_hints.dfy
  
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


  (h_0 : b ≠ c ∧ b ≠ d ∧ b.size == c.size + d.size)
  (h_1 : Sorted(c[..]) ∧ Sorted(d[..]))
  (h_2 : i0 ≤ c.size ∧ j0 ≤ d.size ∧ i0 + j0 ≤ b.size)
  (h_3 : InvSubSet(b[..],c[..],d[..],i0,j0))
  (h_4 : InvSorted(b[..],c[..],d[..],i0,j0))
  (h_5 : i0 + j0 < b.size)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks