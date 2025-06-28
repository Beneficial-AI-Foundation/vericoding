// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn main(n: int) -> (i: int, x: int, y: int)
    requires
        n >= 0
    ensures
        (i % 2 != 0) || (x == 2 * y)
{
    return (0, 0, 0);
}

}