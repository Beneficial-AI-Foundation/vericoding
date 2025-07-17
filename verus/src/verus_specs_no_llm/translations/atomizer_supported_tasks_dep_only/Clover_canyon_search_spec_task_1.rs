// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CanyonSearch(a: Vec<int>, b: Vec<int>) -> d:nat
    requires
        a.len() !=0 && b.len()!=0,
        forall |i: int, j: int| 0<=i<j<a.len() ==> a.index(i)<=a.index(j),
        forall |i: int, j: int| 0<=i<j<b.len() ==> b.index(i)<=b.index(j)
    ensures
        exists |i: int, j: int| 0<=i<a.len() && 0<=j<b.len() && d==if a.index(i) < b.index(j) then (b.index(j)-a.index(i)) else (a.index(i)-b.index(j)),
        forall |i: int, j: int| 0<=i<a.len() && 0<=j<b.len() ==> d<=if a.index(i) < b.index(j) then (b.index(j)-a.index(i)) else (a.index(i)-b.index(j))
;

proof fn lemma_CanyonSearch(a: Vec<int>, b: Vec<int>) -> (d: nat)
    requires
        a.len() !=0 && b.len()!=0,
        forall |i: int, j: int| 0<=i<j<a.len() ==> a.index(i)<=a.index(j),
        forall |i: int, j: int| 0<=i<j<b.len() ==> b.index(i)<=b.index(j)
    ensures
        exists |i: int, j: int| 0<=i<a.len() && 0<=j<b.len() && d==if a.index(i) < b.index(j) then (b.index(j)-a.index(i)) else (a.index(i)-b.index(j)),
        forall |i: int, j: int| 0<=i<a.len() && 0<=j<b.len() ==> d<=if a.index(i) < b.index(j) then (b.index(j)-a.index(i)) else (a.index(i)-b.index(j))
{
    0
}

}