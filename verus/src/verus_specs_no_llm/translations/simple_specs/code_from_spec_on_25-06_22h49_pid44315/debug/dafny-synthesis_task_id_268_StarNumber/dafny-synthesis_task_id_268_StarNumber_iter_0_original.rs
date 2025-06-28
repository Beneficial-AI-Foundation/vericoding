// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StarNumber(n: int) -> (star: int)
    requires
        n >= 0
    ensures
        star == 6 * n * (n - 1) + 1
{
    return 0;
}

}