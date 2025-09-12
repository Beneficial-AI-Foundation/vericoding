/-
  Port of vericoding_dafnybench_0049_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsPalindrome (x : seq<char>) : Bool :=
  sorry  -- TODO: implement function body

theorem IsPalindrome_spec (x : seq<char>) (result : Bool) :=
  : result <→ (∀ i :: 0 ≤ i < |x| → x[i]! == x[|x| - i - 1])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks