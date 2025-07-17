// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn below(first: Bases, second: Bases) -> bool {
    first == second |
    first == A .len() 
    (first == C && (second ==  G .len() second == T)) .len() 
    (first == G && second == T) .len()|
    second == T
}
spec fn bordered(s: Seq<Bases>) -> bool {
    forall |j: int, k: int| 0 <= j < k < s.len() ==> below(s.index(j), s.index(k))
}

spec fn spec_Exchanger(s: Seq<Bases>, x: nat, y: nat) -> t: seq<Bases>
    requires
        0 < s.len() && x < s.len() && y < s.len()
    ensures
        t.len() == s.len(),
        forall |b: nat| 0 <= b < s.len() && b != x && b != y ==> t.index(b) == s.index(b),
        t.index(x) == s.index(y) && s.index(x) == t.index(y),
        multiset(s) == multiset(t)
;

proof fn lemma_Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len()
    ensures
        t.len() == s.len(),
        forall |b: nat| 0 <= b < s.len() && b != x && b != y ==> t.index(b) == s.index(b),
        t.index(x) == s.index(y) && s.index(x) == t.index(y),
        multiset(s) == multiset(t)
{
    Seq::empty()
}

}