/-
  Port of dafny-synthesis_task_id_790_IsEvenAtIndexEven.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsEvenAtIndexEven (lst : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem IsEvenAtIndexEven_spec (lst : seq<int>) (result : Bool) :=
  : result <→ ∀ i :: 0 ≤ i < |lst| → (IsEven(i) → IsEven(lst[i]!))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks