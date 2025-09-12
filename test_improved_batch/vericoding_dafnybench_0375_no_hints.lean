/-
  Port of vericoding_dafnybench_0375_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def isPalindrome (s : Array Char) : Bool :=
  sorry  -- TODO: implement function body

theorem isPalindrome_spec (s : Array Char) (result : Bool) :=
  (h_0 : 1≤ s.size ≤ 200000)
  : result <→ (∀ i:: 0 ≤ i < s.size / 2 → s[i]! == s[s.size - 1 - i])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks