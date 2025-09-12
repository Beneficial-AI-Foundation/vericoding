/-
  Port of vericoding_dafnybench_0053_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LongestCommonPrefix (str1 : seq<char>) (str2 : seq<char>) : seq<char> :=
  sorry  -- TODO: implement function body

theorem LongestCommonPrefix_spec (str1 : seq<char>) (str2 : seq<char>) (prefix : seq<char>) :=
  : |prefix| ≤ |str1| ∧ prefix == str1[0..|prefix|]∧ |prefix| ≤ |str2| ∧ prefix == str2[0..|prefix|] ∧ |prefix|==|str1| ∨ |prefix|==|str2| ∨ (str1[|prefix|]≠str2[|prefix|])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks