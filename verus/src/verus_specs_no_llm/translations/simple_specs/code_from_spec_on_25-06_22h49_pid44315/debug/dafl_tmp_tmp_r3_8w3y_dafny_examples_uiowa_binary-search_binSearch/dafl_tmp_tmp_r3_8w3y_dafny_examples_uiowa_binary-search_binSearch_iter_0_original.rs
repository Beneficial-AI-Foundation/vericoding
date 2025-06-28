// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn binSearch(a: Vec<int>, K: int) -> (b: bool)
    requires
        isSorted(a)
    ensures
        b == exists i:nat :: i < a.len() && a.spec_index(i) == K
{
    return false;
}

}