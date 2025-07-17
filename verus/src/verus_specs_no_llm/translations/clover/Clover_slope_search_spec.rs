// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SlopeSearch(a: array2<int>, key: int) -> m:int, n:int
    requires
        forall |i: int, j: int, j': int|0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a.index(i,j)<=a.index(i,j'),
        forall |i: int, i': int, j: int|0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a.index(i,j)<=a.index(i',j),
        exists |i: int, j: int| 0<=i<a.Length0 && 0<=j<a.Length1 && a.index(i,j)==key
    ensures
        0<=m<a.Length0 && 0<=n<a.Length1,
        a.index(m,n)==key
;

proof fn lemma_SlopeSearch(a: array2<int>, key: int) -> (m: int, n: int)
    requires
        forall |i: int, j: int, j': int|0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a.index(i,j)<=a.index(i,j'),
        forall |i: int, i': int, j: int|0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a.index(i,j)<=a.index(i',j),
        exists |i: int, j: int| 0<=i<a.Length0 && 0<=j<a.Length1 && a.index(i,j)==key
    ensures
        0<=m<a.Length0 && 0<=n<a.Length1,
        a.index(m,n)==key
{
    (0, 0)
}

}