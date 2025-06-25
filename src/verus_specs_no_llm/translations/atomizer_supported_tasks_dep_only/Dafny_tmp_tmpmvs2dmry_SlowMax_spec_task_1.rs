// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn slow_max(a: nat, b: nat) -> (z: nat)
    ensures z == max(a, b)
{
}

}