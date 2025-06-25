// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ElementWiseSubtraction(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires a != null and b != null,
             a.len() == b.len()
    ensures result != null,
            result.len() == a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i]
{
}

}