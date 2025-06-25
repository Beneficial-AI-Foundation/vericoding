// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn mult(a: int, b: int) -> (x: int)
    requires
        a >= 0 && b >= 0
    ensures
        x == a * b
{
    return 0;
}

}