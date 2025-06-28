// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn peasantMult(a: int, b: int) -> (r: int)
    requires
        b > 0
    ensures
        r == a * b
{
    return 0;
}

}