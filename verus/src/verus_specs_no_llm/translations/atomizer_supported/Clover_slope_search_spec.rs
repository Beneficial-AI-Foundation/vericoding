// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn SlopeSearch(a: array2<int>, key: int) -> (m: int, n: int)
    requires
        forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a.spec_index(i,j)<=a.spec_index(i,j'),
        forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a.spec_index(i,j)<=a.spec_index(i',j),
        exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a.spec_index(i,j)==key
    ensures
        0<=m<a.Length0 && 0<=n<a.Length1,
        a.spec_index(m,n)==key
{
    return (0, 0);
}

}