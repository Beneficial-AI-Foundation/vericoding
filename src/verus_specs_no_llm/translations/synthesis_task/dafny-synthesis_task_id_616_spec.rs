// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ElementWiseModulo(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires a != null and b != null,
             a.len() == b.len(),
             forall|i: int| 0 <= i < b.len() ==> b[i] != 0
    ensures result != null,
            result.len() == a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i]
{
}

}