// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMin(a: Vec<int>, lo: nat) -> (minIdx: nat)
    requires
        a != null && a.len() > 0 && lo < a.len()
    ensures
        lo <= minIdx < a.len(),
        forall x :: lo <= x < a.len() ==> a.spec_index(minIdx) <= a.spec_index(x)
{
    return 0;
}

}