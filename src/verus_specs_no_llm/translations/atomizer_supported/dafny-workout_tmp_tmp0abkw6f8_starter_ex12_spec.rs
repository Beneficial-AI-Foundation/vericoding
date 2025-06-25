// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindMax(a: Vec<int>) -> (max_idx: nat)
    requires a.len() > 0
    ensures 0 <= max_idx < a.len(),
            forall|j: int| 0 <= j < a.len() ==> a[max_idx] >= a[j]
{
}

}