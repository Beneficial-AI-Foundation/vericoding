// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LastDigit(n: int) -> (d: int)
    requires
        n >= 0
    ensures
        0 <= d < 10,
        n % 10 == d
{
    return 0;
}

}