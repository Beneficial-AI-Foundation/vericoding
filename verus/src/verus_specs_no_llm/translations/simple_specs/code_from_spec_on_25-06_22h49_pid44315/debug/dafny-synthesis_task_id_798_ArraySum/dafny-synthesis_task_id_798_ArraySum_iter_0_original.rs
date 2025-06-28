// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySum(a: Vec<int>) -> (result: int)
    ensures
        result == sumTo(a, a.len())
{
    return 0;
}

}