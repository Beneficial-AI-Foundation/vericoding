// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn HasCommonElement(a: Vec<int>, b: Vec<int>) -> (result: bool)
    requires a != null and b != null
    ensures result ==> exists|i: int, j: int| 0 <= i < a.len() and 0 <= j < b.len() and a[i] == b[j],
            !result ==> forall|i: int, j: int| 0 <= i < a.len() and 0 <= j < b.len() ==> a[i] != b[j]
{
}

}