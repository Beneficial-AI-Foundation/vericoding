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

fn m2(x: nat) -> (y: int)
    requires
        x <= -1
    ensures
        y > x && y < x
{
    return 0;
}

}