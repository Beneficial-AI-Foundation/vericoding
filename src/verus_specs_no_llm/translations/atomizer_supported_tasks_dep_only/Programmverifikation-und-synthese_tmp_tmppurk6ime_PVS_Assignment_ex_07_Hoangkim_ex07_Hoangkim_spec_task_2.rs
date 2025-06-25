// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindMin(a: Vec<int>, lo: nat) -> (minIdx: nat)
    requires a != null and a.len() > 0 and lo < a.len()
    ensures lo <= minIdx < a.len(),
            forall|x: int| lo <= x < a.len() ==> a[minIdx] <= a[x]
{
}

}