// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ComputeFib(n: nat) -> (x: nat)
    ensures x == Fib(n)
{
}

}