/-
  Port of vericoding_dafnybench_0210_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Add (x : Nat) (y : Nat) : Nat :=
  match y case Zero => x case S(y') => S(Add(x, y'))

def Size (l : List<Nat>) : Nat :=
  if l.Nil? then Zero else S(Size(l.tail))

def Concatenation (l1 : List<Nat>) (l2 : List<Nat>) : List :=
  match l1 case Nil => l2 case Append(head1, tail1) => match l2 case Nil => l1 case Append(_, _) => Append(head1, Concatenation(tail1, l2))

def ReverseList (l : List<Nat>) : List :=
  if l.Nil? then Nil else Concatenation(ReverseList(l.tail), Append(l.head, Nil))

end DafnyBenchmarks