// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
    requires 0 <= from < to <= a.len()
    ensures from <= index < to,
            forall|k: int| from <= k < to ==> a[k] >= a[index]
{
}

}