/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_COST-verif-comp-2011-3-TwoDuplicates_Search.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Search (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem Search_spec (a : Array Int) (p : Int) :=
  (h_0 : 4 ≤ a.size;)
  (h_1 : ∃ p,q :: p ≠ q ∧ IsDuplicate(a, p) ∧ IsDuplicate(a, q);  // two distinct duplicates exist)
  (h_2 : ∀ i :: 0 ≤ i < a.size → 0 ≤ a[i]! < a.size - 2;  // the elements of "a" in the range [0.. a.size-2])
  : p ≠ q ∧ IsDuplicate(a, p) ∧ IsDuplicate(a, q);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks