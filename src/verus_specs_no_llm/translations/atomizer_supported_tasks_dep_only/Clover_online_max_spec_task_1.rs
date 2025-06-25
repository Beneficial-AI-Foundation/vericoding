// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn onlineMax(a: Vec<int>, x: int) -> ghost m: int, p: int
    requires 1<=x<a.len(),
             a.len()!=0
    ensures x<=p<a.len(),
            forall|i: int|0<=i<x==> a[i]<=m,
            exists|i: int|0<=i<x and a[i]==m,
            x<=p<a.len()-1 ==> (forall|i: int|0<=i<p ==> a[i]<a[p]),
            (forall|i: int|x<=i<a.len() and a[i]<=m) ==> p==a.len()-1
{
}

}