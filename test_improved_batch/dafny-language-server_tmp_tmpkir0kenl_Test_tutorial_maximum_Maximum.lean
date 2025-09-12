/-
  Port of dafny-language-server_tmp_tmpkir0kenl_Test_tutorial_maximum_Maximum.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Maximum (values : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem Maximum_spec (values : seq<int>) (max : Int) :=
  (h_0 : values ≠ [])
  : max in values ∧ ∀ i | 0 ≤ i < |values| :: values[i]! ≤ max
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks