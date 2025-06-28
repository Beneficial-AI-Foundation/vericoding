// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Pow(a: nat, n: nat) -> (y: nat)
    ensures
        y == pow(a, n)
{
    return 0;
}

}