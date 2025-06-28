// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxArray(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= max,
        exists i :: 0 <= i < a.len() && a.spec_index(i) == max
{
    return 0;
}

}