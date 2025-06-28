// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mult(a: int, b: int) -> (x: int)
    requires
        a >= 0 && b >= 0
    ensures
        x == a * b
{
    return 0;
}

}