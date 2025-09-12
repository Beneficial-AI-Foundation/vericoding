/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems_sumElemsB.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumR (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumL (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumV (v : Array Int) (c : Int) (f : Int) : Int :=
  lemma ArrayFacts<T>() ensures ∀ v : array<T>  :: v[..v.size] == v[..]; ensures ∀ v : array<T>  :: v[0..] == v[..]; ensures ∀ v : array<T>  :: v[0..v.size] == v[..]; ensures ∀ v : array<T>  ::|v[0..v.size]|==v.size; ensures ∀ v : array<T> | v.size≥1 ::|v[1..v.size]|==v.size-1; ensures ∀ v : array<T>  ::∀ k : nat | k < v.size :: v[..k+1][..k] == v[..k] // ensures ∀ v:array<Int>,i,j | 0≤i≤j≤v.size :: SumR(v[i..j])==SumL(v[i..j]) // <vc-helpers> // </vc-helpers> method sumElemsB(v:array<Int>) returns (sum:Int) //ensures sum==SumL(v[0..v.size]) ensures sum==SumR(v[0..v.size]) // <vc-code> assume false; } // </vc-code>

end DafnyBenchmarks