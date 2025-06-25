// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn binSearch(a: Vec<int>, K: int) -> (b: bool)
    requires isSorted(a)
    ensures b == exists i:nat :: i < a.len() and a[i] == K
{
}

}