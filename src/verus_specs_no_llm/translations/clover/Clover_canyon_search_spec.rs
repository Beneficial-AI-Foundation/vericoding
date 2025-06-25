// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CanyonSearch(a: Vec<int>, b: Vec<int>) -> (d: nat)
    requires a.len() !=0 and b.len()!=0,
             forall|i: int, j: int| 0<=i<j<a.len() ==> a[i]<=a[j],
             forall|i: int, j: int| 0<=i<j<b.len() ==> b[i]<=b[j]
    ensures exists|i: int, j: int| 0<=i<a.len() and 0<=j<b.len() and d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]),
            forall|i: int, j: int| 0<=i<a.len() and 0<=j<b.len() ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
}

}