// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountArrays(arrays: Seq<Vec<int>>) -> (count: int)
    ensures
        count >= 0,
        count == arrays.len()
{
    return 0;
}

}