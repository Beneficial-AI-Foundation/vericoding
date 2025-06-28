// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn bar(x: int, y: int) -> (r: int)
    requires
        y >= 0
    ensures
        r == x + y
{
    return 0;
}

}