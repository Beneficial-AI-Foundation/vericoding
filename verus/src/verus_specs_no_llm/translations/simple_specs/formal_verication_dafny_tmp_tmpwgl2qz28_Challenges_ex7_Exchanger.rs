// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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