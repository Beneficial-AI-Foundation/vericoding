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

fn slow_max(a: nat, b: nat) -> (z: nat)
    ensures
        z == max(a, b)
{
    return 0;
}

}