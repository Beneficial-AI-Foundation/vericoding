// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleConditions(x: int) -> (r: int)
    requires
        x % 2 == 0
    ensures
        r == 3 * x
{
    return 3 * x;
}

}