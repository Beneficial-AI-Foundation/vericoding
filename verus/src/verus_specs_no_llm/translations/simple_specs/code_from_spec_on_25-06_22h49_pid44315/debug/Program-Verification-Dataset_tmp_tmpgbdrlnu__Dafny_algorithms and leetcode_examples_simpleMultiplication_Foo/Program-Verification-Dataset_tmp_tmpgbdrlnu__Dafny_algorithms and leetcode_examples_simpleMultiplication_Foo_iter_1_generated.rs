// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Foo(y: int, x: int) -> (z: int)
    requires
        0 <= y
    ensures
        z == x*y
{
    return x * y;
}

}