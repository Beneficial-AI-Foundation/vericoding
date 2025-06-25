// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn appendArray(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures c.len() == a.len() + b.len(),
            forall|i: int| 0 <= i < a.len() ==> a[i] == c[i],
            forall|i: int| 0 <= i < b.len() ==> b[i] == c[a.len() + i]
{
}

}