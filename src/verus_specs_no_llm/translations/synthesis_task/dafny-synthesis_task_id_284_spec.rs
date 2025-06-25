// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AllElementsEqual(a: Vec<int>, n: int) -> (result: bool)
    requires a != null
    ensures result ==> forall|i: int| 0 <= i < a.len() ==> a[i] == n,
            !result ==> exists|i: int| 0 <= i < a.len() and a[i] != n
{
}

}