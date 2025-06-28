// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> (m: int)
    requires
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a.spec_index(i) > b.spec_index(j) ==> m == a.spec_index(i),
        a.spec_index(i) <= b.spec_index(j) ==> m == b.spec_index(j)
{
    return 0;
}

}