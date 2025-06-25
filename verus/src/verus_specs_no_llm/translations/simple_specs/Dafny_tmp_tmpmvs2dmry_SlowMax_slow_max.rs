// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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