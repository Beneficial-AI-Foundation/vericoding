// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Min(x: int, y: int) -> (m: int)
    ensures m <= x and m <= y,
            m == x or m == y
{
}

}