// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DivMod1(a: int, b: int) -> (q: int, r: int)
    requires
        b > 0 && a >= 0
    ensures
        a == b*q + r && 0 <= r < b
//decreases *
{
    return (0, 0);
}

}