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
        b == fib(n)
{
    return 0;
}

}