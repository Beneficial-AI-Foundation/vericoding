// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MedianLength(a: int, b: int) -> (median: int)
    requires
        a > 0 && b > 0
    ensures
        median == (a + b) / 2
{
    return 0;
}

}