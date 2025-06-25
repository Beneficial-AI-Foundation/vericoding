// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn strictNegative(v: Vec<int>, i: int, j: int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}


// ATOM 

predicate positive(s:seq<int>) -> bool {
    forall|u: int|0<=u<s.len() ==> s[u]>=0
}
spec fn isPermutation(s: Seq<int>, t: Seq<int>) -> bool {
    multiset(s)==multiset(t)
}

fn separate(v: Vec<int>) -> i: int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v, i, v.Length
    ensures 0<=i<=v.len(),
            positive(v[0..i]) and strictNegative(v,i,v.len()),
            isPermutation(v[0..v.len()], old(v[0..v.len()]))
{
}

}