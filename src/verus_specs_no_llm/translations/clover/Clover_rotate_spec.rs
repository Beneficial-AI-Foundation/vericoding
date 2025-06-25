// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn rotate(a: Vec<int>, offset: int) -> (b: Vec<int>)
    requires 0<=offset
    ensures b.len()==a.len(),
            forall|i: int|0<=i<a.len() ==>  b[i]==a[(i+offset)%a.len()]
{
}

}