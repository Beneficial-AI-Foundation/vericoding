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

fn onlineMax(a: Vec<int>, x: int) -> (ghost m: int, p: int)
    requires
        1<=x<a.len(),
        a.len()!=0
    ensures
        x<=p<a.len(),
        forall i::0<=i<x==> a.spec_index(i)<=m,
        exists i::0<=i<x && a.spec_index(i)==m,
        x<=p<a.len()-1 ==> (forall i::0<=i<p ==> a.spec_index(i)<a.spec_index(p)),
        (forall i::x<=i<a.len() && a.spec_index(i)<=m) ==> p==a.len()-1
{
    return (0, 0);
}

}