// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ComputePower(N: int) -> (y: nat)
    requires N >= 0
    ensures y == Power(N)
{
}

}