// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Forbid42(x: int, y: int) -> (z: int)
    requires y != 42;
    ensures z == x/(42-y);
{
}

}