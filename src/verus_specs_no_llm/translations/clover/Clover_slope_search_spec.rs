// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SlopeSearch(a: array2<int>, key: int) -> m: int, n: int
    requires forall|i: int, j: int, j': int|0<=i<a.Length0 and 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j'],
             forall|i: int, i': int, j: int|0<=i<i'<a.Length0 and 0<=j<a.Length1 ==> a[i,j]<=a[i',j],
             exists|i: int, j: int| 0<=i<a.Length0 and 0<=j<a.Length1 and a[i,j]==key
    ensures 0<=m<a.Length0 and 0<=n<a.Length1,
            a[m,n]==key
{
}

}