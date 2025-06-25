// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn addArrays(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires a.len() == b.len()
    ensures b.len() == c.len(),
            forall i:int :: 0 <= i <c.len() ==> c[i] == a[i] + b[i]
{
}

}