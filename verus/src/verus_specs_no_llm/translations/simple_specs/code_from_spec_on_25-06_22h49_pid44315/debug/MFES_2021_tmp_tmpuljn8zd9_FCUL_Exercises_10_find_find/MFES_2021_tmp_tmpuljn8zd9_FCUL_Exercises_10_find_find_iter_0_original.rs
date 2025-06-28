// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn find(a: Vec<int>, key: int) -> (index: int)
    requires
        a.len() > 0
    ensures
        0 <= index <= a.len(),
        index < a.len() ==> a.spec_index(index) == key
{
    return 0;
}

}