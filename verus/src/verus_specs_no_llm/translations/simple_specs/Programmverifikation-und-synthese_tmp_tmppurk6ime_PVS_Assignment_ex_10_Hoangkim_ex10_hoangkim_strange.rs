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

fn q(x: nat, y: nat) -> (z: nat)
    requires
        y - x > 2
    ensures
        x < z*z < y


// SPEC

method strange(),
        1==2
{
    return 0;
}

}