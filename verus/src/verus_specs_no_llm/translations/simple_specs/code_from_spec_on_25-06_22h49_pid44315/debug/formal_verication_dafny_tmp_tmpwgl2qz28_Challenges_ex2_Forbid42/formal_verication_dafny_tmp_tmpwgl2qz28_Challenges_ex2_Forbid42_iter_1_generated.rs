// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Forbid42(x: int, y: int) -> (z: int)
    requires
        y != 42
    ensures
        z == x/(42-y)
{
    x / (42 - y)
}

}