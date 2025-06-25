// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn main(n: int) -> (a: int, b: int)
    requires
        n >= 0
    ensures
        a + b == 3 * n
{
    return (0, 0);
}

}