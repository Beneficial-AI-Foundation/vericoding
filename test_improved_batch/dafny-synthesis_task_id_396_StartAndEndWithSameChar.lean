/-
  Port of dafny-synthesis_task_id_396_StartAndEndWithSameChar.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def StartAndEndWithSameChar (s : String) : Bool :=
  sorry  -- TODO: implement function body

theorem StartAndEndWithSameChar_spec (s : String) (result : Bool) :=
  (h_0 : |s| > 0)
  : result <→ s[0]! == s[|s| - 1]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks