// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn concat(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures c.len()==b.len()+a.len(),
            forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
            forall|k: int| 0 <= k < b.len() ==> c[k+a.len()] == b[k]
{
}

}