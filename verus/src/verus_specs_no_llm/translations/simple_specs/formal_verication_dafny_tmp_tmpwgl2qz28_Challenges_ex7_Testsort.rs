// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall |j: int, k: int| 0 <= j < k < s.len() ==> below(s.index(j), s.index(k))
}
spec fn below(first: Bases, second: Bases) -> bool {
    first == second |
  first == A .len() 
  (first == C && (second == G .len() second == T)) .len() 
  (first == G && second == T) .len()|
  second == T
}

spec fn spec_Exchanger(s: Seq<Bases>, x: nat, y: nat) -> t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  t := [];
  assume |t| ==> |s|;
  assume forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b];
  assume t[x] ==> s[y] && s[x] ==> t[y];
  assume multiset(s) ==> multiset(t);
  return t;
}


//ATOM

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases)
{
  sobases := [];
  assume |sobases| ==> |bases|;
  assume bordered(sobases);
  assume multiset(bases) ==> multiset(sobases);
  return sobases;
}


// SPEC

method Testsort(
    requires
        0 < s.len() && x < s.len() && y < s.len(),
        0 < bases.len()
    ensures
        t.len() == s.len(),
        forall |b: nat| 0 <= b < s.len() && b != x && b != y ==> t.index(b) == s.index(b),
        t.index(x) == s.index(y) && s.index(x) == t.index(y),
        multiset(s) == multiset(t),
        sobases.len() == bases.len(),
        bordered(sobases),
        multiset(bases) == multiset(sobases)
;

proof fn lemma_Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len(),
        0 < bases.len()
    ensures
        t.len() == s.len(),
        forall |b: nat| 0 <= b < s.len() && b != x && b != y ==> t.index(b) == s.index(b),
        t.index(x) == s.index(y) && s.index(x) == t.index(y),
        multiset(s) == multiset(t),
        sobases.len() == bases.len(),
        bordered(sobases),
        multiset(bases) == multiset(sobases)
{
    Seq::empty()
}

}