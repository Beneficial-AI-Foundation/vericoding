// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall u::0<=u<s.len() ==> s.spec_index(u)>=0
}
spec fn strictNegative(v: Vec<int>, i: int, j: int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}


//ATOM

predicate isPermutation(s:seq<int>, t: Seq<int>) -> bool {
    multiset(s)==multiset(t)
}

fn separate(v: Vec<int>) -> (i: int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v, i, v.Length)
    ensures
        0<=i<=v.len(),
        positive(v.spec_index(0..i)) && strictNegative(v,i,v.len()),
        isPermutation(v.spec_index(0..v.len()), old(v.spec_index(0..v.len())))
{
    return (0, 0, 0);
}

}