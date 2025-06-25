// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountToAndReturnN(n: int) -> (r: int)
    requires
        n >= 0
    ensures
        r == n
{
    return 0;
}

}