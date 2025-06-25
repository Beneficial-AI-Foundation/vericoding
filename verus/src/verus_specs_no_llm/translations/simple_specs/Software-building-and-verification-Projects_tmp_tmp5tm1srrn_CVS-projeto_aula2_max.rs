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

fn max(a: int, b: int) -> (z: int)
    requires
        true
    ensures
        z >= a || z >= b
{
    return 0;
}

}