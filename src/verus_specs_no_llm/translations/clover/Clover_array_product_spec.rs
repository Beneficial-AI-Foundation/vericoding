// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn arrayProduct(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires a.len()==b.len()
    ensures c.len()==a.len(),
            forall|i: int| 0 <= i< a.len()==> a[i] * b[i]==c[i]
{
}

}