// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minMethod(a: int, b: int) -> (c: int)
    ensures
        c <= a && c <= b,
        c == a || c == b
    // Ou encore:,
        c == min(a, b)
{
    return 0;
}

}