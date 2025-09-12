/-
  Port of summer-school-2020_tmp_tmpn8nf7zf0_chapter02_solutions_exercise03_solution_merge_sort.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def merge_sort (input : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem merge_sort_spec (input : seq<int>) (output : seq<int>) :=
  : SortSpec(input, output)
  := by
  sorry  -- TODO: implement proof

def merge (a : seq<int>) (b : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem merge_spec (a : seq<int>) (b : seq<int>) (output : seq<int>) :=
  (h_0 : IsSorted(a))
  (h_1 : IsSorted(b))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks