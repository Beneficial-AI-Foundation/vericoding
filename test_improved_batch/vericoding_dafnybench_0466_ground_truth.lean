/-
  Port of vericoding_dafnybench_0466_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def length (list : List) : Nat :=
  match list case Nil => 0 case Cons(_, tl) => 1 + length(tl)

def In (x : Int) (list : List<int>) : Nat :=
  sorry  -- TODO: implement complex function body

def append (n0 : Int) (n1 : Int) (n2 : Int) (n3 : Int) (i : List<int>) (j : List<int>) : List :=
  sorry  -- TODO: implement function body

function partition(x: int, l: List<int>): (List<int>, List<int>)
  sorry  -- TODO: implement function body

def sort (min : Int) (max : Int) (i : List<int>) : List :=
  sorry  -- TODO: implement function body

end DafnyBenchmarks