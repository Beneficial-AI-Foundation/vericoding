// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ComputeFib(n: nat) -> (b: nat)
    ensures b == fib(n)  // Do not change this postcondition
{
}

}