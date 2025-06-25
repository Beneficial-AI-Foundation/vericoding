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

fn Foo(y: int, x: int) -> (z: int)
    requires
        0 <= y
    ensures
        z == x*y
{
    return 0;
}

}