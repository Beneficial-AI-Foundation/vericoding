// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0)==is_even
{
    return false;
}

}