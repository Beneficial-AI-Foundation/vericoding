// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires
        0 <= l < r <= a.len()
    ensures
        ret.spec_index(..) == a.spec_index(l..r)
{
    return Vec::new();
}

}