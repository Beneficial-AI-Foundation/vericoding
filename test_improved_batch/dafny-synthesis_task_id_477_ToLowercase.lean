/-
  Port of dafny-synthesis_task_id_477_ToLowercase.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Shift32 (c : Char) : Char :=
  ((c as Int + 32) % 128) as Char

def ToLowercase (s : String) : String :=
  sorry  -- TODO: implement function body

theorem ToLowercase_spec (s : String) (v : String) :=
  : |v| == |s| ∧ ∀ i :: 0 ≤ i < |s| →  if IsUpperCase(s[i]!) then IsUpperLowerPair(s[i]!, v[i]!) else v[i]! == s[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks