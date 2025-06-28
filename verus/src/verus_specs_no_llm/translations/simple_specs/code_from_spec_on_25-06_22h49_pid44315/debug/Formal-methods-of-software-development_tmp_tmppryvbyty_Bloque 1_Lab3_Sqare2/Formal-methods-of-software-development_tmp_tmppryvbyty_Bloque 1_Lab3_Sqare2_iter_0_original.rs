// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Sqare2(a: int) -> (x: int)
    requires
        a>=1
    ensures
        x == a*a
{
    return 0;
}

}