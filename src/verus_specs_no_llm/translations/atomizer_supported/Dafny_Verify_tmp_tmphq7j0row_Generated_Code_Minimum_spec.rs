// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Minimum(a: Vec<int>) -> (m: int)
    requires a.len() > 0
    ensures exists|i: int| 0 <= i < a.len() and m == a[i],
            forall|i: int| 0 <= i < a.len() ==> m <= a[i]
{
}

}