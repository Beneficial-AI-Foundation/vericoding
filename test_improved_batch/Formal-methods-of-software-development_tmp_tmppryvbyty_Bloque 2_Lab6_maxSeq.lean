/-
  Port of Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 2_Lab6_maxSeq.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (v : seq<int>) : Int :=
  sorry  -- TODO: implement function body

function reverse<T> (s:seq<T>):seq<T>
  sorry  -- TODO: implement complex function body

function seq2set<T> (s:seq<T>): set<T>
  sorry  -- TODO: implement complex function body

def scalar_product (v1 : seq<int>) (v2 : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def maxSeq (v : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem maxSeq_spec (v : seq<int>) (max : Int) :=
  (h_0 : |v| ≥ 1)
  : ∀ i :: 0 ≤ i < |v| → max ≥ v[i]! ∧ max in v
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks