/-
  Port of vericoding_dafnybench_0018_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fact (n : Nat) : Nat :=
  function factAcc (n:nat, a:Int): Int function factAlt(n:nat):Int lemma factAcc_correct (n:nat, a:Int) ensures factAcc(n, a) == a*fact(n) } lemma factAlt_correct (n:nat) ensures factAlt(n) == fact(n) factAcc_correct(n,1); } datatype List<T> = Nil | Cons(T, List<T>) function length<T> (l: List<T>) : nat match l case Nil => 0 case Cons(_, r) => 1 + length(r) } lemma {:induction false} length_non_neg<T> (l:List<T>) ensures length(l) ≥ 0 match l case Nil => case Cons(_, r) => length_non_neg(r); //  assert ∀ k : Int, k ≥ 0 → 1 + k ≥ 0; } function lengthTL<T> (l: List<T>, acc: nat) : nat match l case Nil => acc case Cons(_, r) => lengthTL(r, 1 + acc) } lemma {:induction false}lengthTL_aux<T> (l: List<T>, acc: nat) ensures lengthTL(l, acc) == acc + length(l) match l case Nil => assert acc + length<T>(Nil) == acc; case Cons(_, r) => lengthTL_aux(r, acc + 1); } lemma lengthEq<T> (l: List<T>) ensures length(l) == lengthTL(l,0) lengthTL_aux(l, 0); }

end DafnyBenchmarks