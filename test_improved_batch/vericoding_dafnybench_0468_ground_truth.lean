/-
  Port of vericoding_dafnybench_0468_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def append (xs : List) (ys : List) : List :=
  match xs case Nil => ys case Cons(x, xs') => Cons(x, append(xs', ys))

function Return<T>(a: T): List
  Cons(a, Nil)

function Bind<T,U>(xs: List<T>, f: T -> List<U>): List<U>
  match xs case Nil => Nil case Cons(x, xs') => append(f(x), Bind(xs', f))

end DafnyBenchmarks