// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn fibIter(n: nat) -> (a: nat)
    requires
        n > 0
    ensures
        a == fib(n)
{
    return 0;
}

}