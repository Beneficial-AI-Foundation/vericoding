// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitArray(arr: Vec<int>, L: int) -> (firstPart: Seq<int>, secondPart: Seq<int>)
    requires
        0 <= L <= arr.len()
    ensures
        firstPart.len() == L,
        secondPart.len() == arr.len() - L,
        firstPart + secondPart == arr.spec_index(..)
{
    let firstPart = arr.spec_index(0..L);
    let secondPart = arr.spec_index(L..arr.len());
    
    // Verus can automatically prove the postconditions from the slice operations
    (firstPart, secondPart)
}

}