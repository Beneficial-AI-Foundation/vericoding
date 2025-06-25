// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn random(a: int, b: int) -> (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: Seq<T>, s2: Seq<T>)
    requires
        a <= b,
        multiset(s1) == multiset(s2)
    ensures
        a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>),
        t in s1 <==> t in s2
{
    return (0, Seq::empty(), Seq::empty());
}

}