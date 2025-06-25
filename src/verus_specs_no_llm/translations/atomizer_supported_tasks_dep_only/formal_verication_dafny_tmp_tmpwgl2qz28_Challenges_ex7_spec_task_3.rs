// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 0 < s.len() and x < s.len() and y < s.len()
    ensures t.len() == s.len(),
            forall b:nat :: 0 <= b < s.len() and b != x and b != y ==> t[b] == s[b],
            t[x] == s[y] and s[x] == t[y],
            multiset(s) == multiset(t)
{
}

}