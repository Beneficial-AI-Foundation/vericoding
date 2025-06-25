// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minArray(a: Vec<int>) -> (m: int)
    requires
        a!= null && a.len() > 0
    ensures
        forall k | 0 <= k < a.len() :: m <= a.spec_index(k),
        exists k | 0 <= k < a.len() :: m == a.spec_index(k)
{
    return 0;
}

}