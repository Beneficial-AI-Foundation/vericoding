/-
  Port of AssertivePrograming_tmp_tmpwf43uz0e_MergeSort_MergeLoop.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MergeLoop (b : Array Int) (c : Array Int) (d : Array Int) (i0 : Nat) (j0 : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem MergeLoop_spec (b : Array Int) (c : Array Int) (d : Array Int) (i0 : Nat) (j0 : Nat) (i : Nat) :=
  (h_0 : b ≠ c ∧ b ≠ d ∧ b.size == c.size + d.size)
  (h_1 : Sorted(c[..]) ∧ Sorted(d[..]))
  (h_2 : i0 ≤ c.size ∧ j0 ≤ d.size ∧ i0 + j0 ≤ b.size)
  (h_3 : InvSubSet(b[..],c[..],d[..],i0,j0))
  (h_4 : InvSorted(b[..],c[..],d[..],i0,j0))
  (h_5 : i0 + j0 < b.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks