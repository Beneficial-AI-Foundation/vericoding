// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn BinarySearch(a: Vec<int>, x: int) -> (index: int)
    requires
        sorted(a)
    ensures
        0 <= index < a.len() ==> a.spec_index(index) == x,
        index == -1 ==> forall i : int :: 0 <= i < a.len() ==> a.spec_index(i) != x
{
    return 0;
}

}