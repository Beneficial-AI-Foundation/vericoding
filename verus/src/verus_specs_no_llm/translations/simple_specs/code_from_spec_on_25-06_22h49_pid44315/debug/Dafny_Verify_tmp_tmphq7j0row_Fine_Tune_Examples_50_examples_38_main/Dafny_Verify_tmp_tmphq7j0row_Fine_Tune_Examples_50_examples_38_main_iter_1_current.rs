// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main(n: int) -> (i: int, x: int, y: int)
    requires
        n >= 0
    ensures
        (i % 2 != 0) || (x == 2 * y)
{
    return (n, 0, 0);
}

}