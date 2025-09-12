/-
  Port of dafny-synthesis_task_id_600_IsEven.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsEven (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsEven_spec (n : Int) (result : Bool) :=
  : result <→ n % 2 == 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks