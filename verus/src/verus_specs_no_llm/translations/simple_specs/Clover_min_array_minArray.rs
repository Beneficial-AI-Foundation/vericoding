// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minArray(a: Vec<int>) -> (r: int)
    requires
        a.len() > 0
    ensures
        forall i :: 0 <= i < a.len() ==> r <= a.spec_index(i),
        exists i :: 0 <= i < a.len() && r == a.spec_index(i)
{
    return 0;
}

}