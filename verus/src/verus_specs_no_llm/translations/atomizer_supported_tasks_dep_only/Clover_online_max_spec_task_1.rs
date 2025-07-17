// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_onlineMax(a: Vec<int>, x: int) -> ghost m:int, p:int
    requires
        1<=x<a.len(),
        a.len()!=0
    ensures
        x<=p<a.len(),
        forall |i: int|0<=i<x==> a.index(i)<=m,
        exists |i: int|0<=i<x && a.index(i)==m,
        x<=p<a.len()-1 ==> (forall |i: int|0<=i<p ==> a.index(i)<a.index(p)),
        (forall |i: int|x<=i<a.len() && a.index(i)<=m) ==> p==a.len()-1
;

proof fn lemma_onlineMax(a: Vec<int>, x: int) -> (ghost m: int, p: int)
    requires
        1<=x<a.len(),
        a.len()!=0
    ensures
        x<=p<a.len(),
        forall |i: int|0<=i<x==> a.index(i)<=m,
        exists |i: int|0<=i<x && a.index(i)==m,
        x<=p<a.len()-1 ==> (forall |i: int|0<=i<p ==> a.index(i)<a.index(p)),
        (forall |i: int|x<=i<a.len() && a.index(i)<=m) ==> p==a.len()-1
{
    (0, 0)
}

}