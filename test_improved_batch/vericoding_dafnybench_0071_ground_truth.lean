/-
  Port of vericoding_dafnybench_0071_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SlopeSearch (a : array2<int>) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SlopeSearch_spec (a : array2<int>) (key : Int) (m : Int) :=
  (h_0 : ∀ i,j,j'::0≤i<a.Length0 ∧ 0≤j<j'<a.Length1 → a[i,j]≤a[i,j'])
  (h_1 : ∀ i,i',j::0≤i<i'<a.Length0 ∧ 0≤j<a.Length1 → a[i,j]≤a[i',j])
  (h_2 : ∃ i,j :: 0≤i<a.Length0 ∧ 0≤j<a.Length1 ∧ a[i,j]==key)
  : 0≤m<a.Length0 ∧ 0≤n<a.Length1 ∧ a[m,n]==key
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks