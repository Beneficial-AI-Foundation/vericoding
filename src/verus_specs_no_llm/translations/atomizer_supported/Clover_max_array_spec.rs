// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn maxArray(a: Vec<int>) -> (m: int)
    requires a.len() >= 1
    ensures forall|k: int| 0 <= k < a.len() ==> m >= a[k],
            exists|k: int| 0 <= k < a.len() and m == a[k]
{
}

}