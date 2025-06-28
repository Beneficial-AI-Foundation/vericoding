// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Swap(a: int, b: int) -> (result: Seq<int>)
    ensures
        result.len() == 2,
        result.spec_index(0) == b,
        result.spec_index(1) == a
{
    return Seq::empty();
}

}