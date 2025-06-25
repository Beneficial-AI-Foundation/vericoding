// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn minArray(a: Vec<int>) -> (r: int)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
            exists|i: int| 0 <= i < a.len() and r == a[i]
{
}

}