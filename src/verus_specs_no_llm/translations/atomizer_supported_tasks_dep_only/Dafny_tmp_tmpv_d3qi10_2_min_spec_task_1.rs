// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn minMethod(a: int, b: int) -> (c: int)
    ensures c <= a and c <= b,
            c == a or c == b
    // Ou encore:,
            c == min(a, b)
{
}

}