/-
  Port of vericoding_dafnybench_0098_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumR (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumL (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumV (v : Array Int) (c : Int) (f : Int) : Int :=
  lemma ArrayFacts<T>() ensures ∀ v : array<T>  :: v[..v.size] == v[..]; ensures ∀ v : array<T>  :: v[0..] == v[..]; ensures ∀ v : array<T>  :: v[0..v.size] == v[..]; ensures ∀ v : array<T>  ::|v[0..v.size]|==v.size; ensures ∀ v : array<T> | v.size≥1 ::|v[1..v.size]|==v.size-1; ensures ∀ v : array<T>  ::∀ k : nat | k < v.size :: v[..k+1][..k] == v[..k] // ensures ∀ v:array<Int>,i,j | 0≤i≤j≤v.size :: SumR(v[i..j])==SumL(v[i..j]) method sumElems(v:array<Int>) returns (sum:Int) //ensures sum==SumL(v[0..v.size]) ensures sum==SumR(v[..]) //ensures sum==SumV(v,0,v.size) sum:=0; var i:Int; i:=0; while (i<v.size) decreases v.size - i//write invariant 0≤i≤v.size ∧ sum == SumR(v[..i])//write sum:=sum+v[i]!; i:=i+1; } } method sumElemsB(v:array<Int>) returns (sum:Int) //ensures sum==SumL(v[0..v.size]) ensures sum==SumR(v[0..v.size]) ArrayFacts<Int>(); sum:=0; var i:Int; i:=v.size; equalSumsV(); while(i>0) decreases i//write invariant 0≤i≤v.size invariant sum == SumL(v[i..]) == SumR(v[i..]) sum:=sum+v[i-1]; i:=i-1; } }

end DafnyBenchmarks