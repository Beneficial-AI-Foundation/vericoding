// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn fibIter(n: nat) -> (a: nat)
    requires n > 0
    ensures a == fib(n)
{
}

}