// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn random(a: int, b: int) -> r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: Seq<T>, s2: Seq<T>
    requires a <= b,
             multiset(s1) == multiset(s2)
    ensures a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>),
            t in s1 <==> t in s2
{
}

}