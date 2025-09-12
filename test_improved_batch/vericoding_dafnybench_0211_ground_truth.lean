/-
  Port of vericoding_dafnybench_0211_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def inf (n : Conat) : Conat :=
  Succ(inf(n))

def add (x : Conat) (y : Conat) : Conat :=
  match x case Zero => y case Succ(x') => Succ(add(x', y))

def addition (a : Stream<int>) (b : Stream<int>) : Stream :=
  Cons(a.head + b.head, addition(a.tail, b.tail))

def cnst (a : Int) : Stream :=
  Cons(a, cnst(a))

def blink  : Stream :=
  Cons(0, Cons(1, blink()))

def zip (a : Stream<int>) (b : Stream<int>) : Stream :=
  Cons(a.head, Cons(b.head, zip(a.tail, b.tail)))

end DafnyBenchmarks