// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Minimum(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        exists i :: 0 <= i < a.len() && m == a.spec_index(i),
        forall i :: 0 <= i < a.len() ==> m <= a.spec_index(i)
{
    return 0;
}

}