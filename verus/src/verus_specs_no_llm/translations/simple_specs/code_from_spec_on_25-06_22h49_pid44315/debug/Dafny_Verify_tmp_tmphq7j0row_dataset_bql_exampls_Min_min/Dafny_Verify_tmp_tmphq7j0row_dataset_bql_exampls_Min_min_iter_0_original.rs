// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn min(a: Vec<int>, n: int) -> (min: int)
    requires
        0 < n <= a.len()
    ensures
        (exists i : int :: 0 <= i && i < n && a.spec_index(i) == min),
        (forall i : int :: 0 <= i && i < n ==> a.spec_index(i) >= min)
{
    return 0;
}

}