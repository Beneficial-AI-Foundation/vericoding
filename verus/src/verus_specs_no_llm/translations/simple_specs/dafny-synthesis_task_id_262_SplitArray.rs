// Translated from Dafny
use builtin::*;
use builtin_macros::*;

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
    return Seq::empty();
}

}