// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main(n: int) -> i: int, x: int, y: int
    requires n >= 0
    ensures (i % 2 != 0) or (x == 2 * y)
{
}

}