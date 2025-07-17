// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn strictNegative(v: Vec<int>, i: int, j: int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}


// ATOM 

predicate positive(s:seq<int>) -> bool {
    forall |u: int|0<=u<s.len() ==> s.index(u)>=0
}
spec fn isPermutation(s: Seq<int>, t: Seq<int>) -> bool {
    multiset(s)==multiset(t)
}

spec fn spec_separate(v: Vec<int>) -> i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length
    ensures
        0<=i<=v.len(),
        positive(v.index(0..i)) && strictNegative(v,i,v.len()),
        isPermutation(v.index(0..v.len()), old(v.index(0..v.len())))
;

proof fn lemma_separate(v: Vec<int>) -> (i: int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v, i, v.Length)
    ensures
        0<=i<=v.len(),
        positive(v.index(0..i)) && strictNegative(v,i,v.len()),
        isPermutation(v.index(0..v.len()), old(v.index(0..v.len())))
{
    (0, 0, 0)
}

}