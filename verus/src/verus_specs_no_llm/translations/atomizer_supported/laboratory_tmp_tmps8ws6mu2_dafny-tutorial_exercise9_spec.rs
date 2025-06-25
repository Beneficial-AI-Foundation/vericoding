// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeFib(n: nat) -> (b: nat)
    ensures
        b == fib(n)  // Do not change this postcondition
{
    return 0;
}

}