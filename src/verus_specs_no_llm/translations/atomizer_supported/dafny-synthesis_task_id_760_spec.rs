// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn HasOnlyOneDistinctElement(a: Vec<int>) -> (result: bool)
    requires a != null
    ensures result ==> forall|i: int, j: int| 0 <= i < a.len() and 0 <= j < a.len() ==> a[i] == a[j],
            !result ==> exists|i: int, j: int| 0 <= i < a.len() and 0 <= j < a.len() and a[i] != a[j]
{
}

}