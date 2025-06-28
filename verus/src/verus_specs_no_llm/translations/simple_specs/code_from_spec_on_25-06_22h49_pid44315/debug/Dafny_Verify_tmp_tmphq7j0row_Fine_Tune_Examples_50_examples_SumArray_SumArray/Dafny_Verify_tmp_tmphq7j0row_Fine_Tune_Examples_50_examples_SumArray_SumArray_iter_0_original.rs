// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumArray(arr: Vec<int>) -> (sum: int)
    requires
        arr.len() > 0
    ensures
        sum == Sum(arr, arr.len())
{
    return 0;
}

}