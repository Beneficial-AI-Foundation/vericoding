// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMax(a: Vec<int>) -> (max: int)
    requires
        a != null && a.len() > 0
    ensures
        0 <= max < a.len(),
        forall x :: 0 <= x < a.len() ==> a.spec_index(max) >= a.spec_index(x)
{
    return 0;
}

}