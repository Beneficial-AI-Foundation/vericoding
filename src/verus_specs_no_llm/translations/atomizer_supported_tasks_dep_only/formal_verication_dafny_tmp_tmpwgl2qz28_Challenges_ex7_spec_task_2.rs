// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn below(first: Bases, second: Bases) -> bool {
    first == second |
    first == A .len() 
    (first == C and (second ==  G .len() second == T)) .len() 
    (first == G and second == T) .len()|
    second == T
}
spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 0 < s.len() and x < s.len() and y < s.len()
    ensures t.len() == s.len(),
            forall b:nat :: 0 <= b < s.len() and b != x and b != y ==> t[b] == s[b],
            t[x] == s[y] and s[x] == t[y],
            multiset(s) == multiset(t)
{
}

}