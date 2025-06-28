// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (c: int)
    ensures
        a >= b ==> c == a,
        b >= a ==> c == b
{
    return 0;
}

}