/-
  Port of vericoding_dafnybench_0755_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function Length<T>(xs: List<T>): int
  match xs case Nil => 0 case Cons(_, tl) => 1 + Length(tl)

function At<T>(xs: List, i: nat): T
  sorry  -- TODO: implement complex function body

def InsertionSort (xs : List<int>) : List :=
  match xs case Nil => Nil case Cons(x, rest) => Insert(x, InsertionSort(rest))

def Insert (x : Int) (xs : List<int>) : List :=
  match xs case Nil => Cons(x, Nil) case Cons(hd, tl) => if x < hd then Cons(x, xs) else Cons(hd, Insert(x, tl))

end DafnyBenchmarks