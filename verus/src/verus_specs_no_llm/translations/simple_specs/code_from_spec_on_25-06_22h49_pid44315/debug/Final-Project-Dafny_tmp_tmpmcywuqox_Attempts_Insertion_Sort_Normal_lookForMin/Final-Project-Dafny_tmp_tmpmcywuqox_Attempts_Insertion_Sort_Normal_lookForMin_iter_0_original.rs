// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn lookForMin(a: Vec<int>, i: int) -> (m: int)
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall k :: i <= k < a.len() ==> a.spec_index(k) >= a.spec_index(m)
{
    return 0;
}

}