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

fn MedianLength(a: int, b: int) -> (median: int)
    requires
        a > 0 && b > 0
    ensures
        median == (a + b) / 2
{
    return 0;
}

}