// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputePower1(N: int) -> (y: nat)
    requires
        N >= 0
//
    ensures
        y == Power(N)
//
{
    return 0;
}

}