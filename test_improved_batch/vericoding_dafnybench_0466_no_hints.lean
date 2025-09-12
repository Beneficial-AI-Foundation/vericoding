/-
  Port of vericoding_dafnybench_0466_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def length (list : List) : Nat :=
  match list case Nil => 0 case Cons(_, tl) => 1 + length(tl)

def In (x : Int) (list : List<int>) : Nat :=
  sorry  -- TODO: implement complex function body

def append (n0 : Int) (n1 : Int) (n2 : Int) (n3 : Int) (i : List<int>) (j : List<int>) : List :=
  match i case Nil => j case Cons(hd, tl) => Cons(hd, append(hd, n1, n2, n3, tl, j))

function partition(x: int, l: List<int>): (List<int>, List<int>)
  sorry  -- TODO: implement function body

def sort (min : Int) (max : Int) (i : List<int>) : List :=
  match i case Nil => Nil case Cons(hd, tl) => var (lo, hi) := partition(hd, tl); var i' := sort(min, hd, lo); var j' := sort(hd, max, hi); append(min, hd, hd, max, i', Cons(hd, j'))

end DafnyBenchmarks