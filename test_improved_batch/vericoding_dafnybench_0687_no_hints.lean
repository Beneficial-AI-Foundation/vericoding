/-
  Port of vericoding_dafnybench_0687_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def add (m : Nat) (n : Nat) : Nat :=
  match m case Zero => n case Succ(m') => Succ(add(m', n))

function size<T>(l: List<T>): nat
  match l case Nil => 0 case Cons(x, l') => size<T>(l') + 1

function app<T>(l1: List<T>, l2: List<T>) : List<T>
  match l1 case Nil => l2 case Cons(x, l1') => Cons(x, app(l1', l2))

function rev<T> (l: List<T>) : List<T>
  match l case Nil => Nil case Cons(x, l') => app(rev(l'), Cons(x, Nil))

end DafnyBenchmarks