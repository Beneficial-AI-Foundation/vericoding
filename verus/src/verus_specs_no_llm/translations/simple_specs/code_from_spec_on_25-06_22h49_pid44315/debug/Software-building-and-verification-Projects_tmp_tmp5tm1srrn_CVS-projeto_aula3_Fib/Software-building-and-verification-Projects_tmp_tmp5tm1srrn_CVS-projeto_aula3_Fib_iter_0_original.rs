// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Fib(n: nat) -> (r: nat)
    ensures
        r == fib(n)
{
    return 0;
}

}