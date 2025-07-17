// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_random(a: int, b: int) -> r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures t in s1 <==> t in s2
{
  calc <==> {
    t in s1;
    t in multiset(s1);
    // Not necessary:
//    t in multiset(s2);
//    t in s2;
  }
/*  
  if (t in s1
    requires
        a <= b,
        multiset(s1) == multiset(s2)
    ensures
        a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>),
        t in s1 <==> t in s2
;

proof fn lemma_random(a: int, b: int) -> (r: int)
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
    (0, Seq::empty(), Seq::empty())
}

}